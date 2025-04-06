#!/usr/bin/python3

__project_name__ = 'cli_to_graphite'
__version__ = '0.37'
__update__ = """
"""

import sys
import pexpect
import re
import time
import schedule
import graphyte
import yaml
import os
import sqlite3
import hashlib
import traceback
import argparse
import copy

from loguru import logger as LoguruLogger
from pexpect import pxssh
from pexpect.pxssh import pxssh as pxssh_class
from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from threading import Lock
from abc import ABC, abstractmethod
from datetime import datetime
from dataclasses import dataclass
from shutil import copyfile
from pexpect.pxssh import ExceptionPxssh

CONFIG_FILE = 'config.yaml'

DEVICES_IN_CMDB = {}


@dataclass
class CMDBQuery:
    """
    class defined query for cmdb request
    """
    name: str
    keys: tuple
    query: str
    params: str


class MutexDeque(deque):
    def __init__(self):
        super().__init__()
        self.mutex = Lock()

    def append(self, item):
        with self.mutex:
            super().append(item)
            logger.debug(f'MutexDeque append item: {item}')

    def extend(self, items):
        with self.mutex:
            super().extend(items)
            logger.debug(f'MutexDeque extend items: {items}')

    def popleft(self):
        with self.mutex:
            logger.debug(f'MutexDeque popleft')
            return super().popleft() if self else None


class NetworkDevice:
    def __init__(self, hostname: str, device_type: str, username: str, password: str, ssh_key: str, schema: str):
        self.hostname = hostname
        self.device_type = device_type
        self.username = username
        self.password = password
        self.ssh_key = ssh_key
        self.schema = schema
        self.connection = None


class NetworkConnections:
    _instance = None

    def __new__(cls, *args, **kwargs):
        if cls._instance is None:
            cls._instance = super().__new__(cls, *args, **kwargs)
        return cls._instance

    def __init__(self):
        self.connections = {}

    def __str__(self):
        return f'Connections: {self.connections}'

    def __setitem__(self, hostname, connection: pxssh_class):
        self.connections[hostname] = connection

    def __delitem__(self, hostname):
        self.connections.pop(hostname, None)

    def __getitem__(self, device: str) -> pxssh_class:
        return self.connections.get(device, None)

    def close_connection(self, con_obj: tuple):
        try:
            hostname = con_obj[0]
            connection = con_obj[1]
            if connection.isalive():
                connection.close()
                if connection.closed:
                    del self.connections[hostname]  # Remove if closed successfully
                logger.info(f"Connection closed successfully: {hostname}")
            else:
                logger.warning(f"Failed to close connection: {hostname}")
        except Exception as err:
            logger.error(f"Error closing connection: {err}")

    def close_all_connections(self):
        with ThreadPoolExecutor() as executor:
            close_conn_result = [executor.submit(self.close_connection, item) for item in self.connections.items()]
            for future in as_completed(close_conn_result):
                result = future.result()
                logger.debug(f"Close connections result: {result}")
            logger.debug(f"Connections count: {len(self.connections)}")


class SSHExpect(ABC):
    type: str
    promt: str
    timeout: int
    dev_mode: str

    def __init__(self, device: NetworkDevice):
        self.hostname = device.hostname
        self.username = device.username
        self.password = device.password
        self.ssh_key = device.ssh_key
        self.options = {"StrictHostKeyChecking": "no"}
        self.connection = None
        self.error = None

    def __enter__(self):
        self.connection: pxssh_class = Connections[self.hostname]
        if self.connection:
            if self.connection.isalive():
                return self
            else:
                del Connections[self.hostname]
        self._new_connection()
        return self

    def __exit__(self, exc_type, exc_value, tb):
        pass

    @property
    @abstractmethod
    def fetch(self):
        pass

    def _new_connection(self):
        try:
            self.connection = pxssh.pxssh(options=self.options)
            self.connection.PROMPT = self.promt
            is_login = self.connection.login(self.hostname, self.username, self.password,
                                             login_timeout=self.timeout,
                                             original_prompt=self.promt,
                                             quiet=False,
                                             auto_prompt_reset=False)
            if is_login and self.connection.before and self.connection.isalive():
                logger.info(f'Created new SSH for {self.hostname}')
                Connections[self.hostname] = self.connection
            else:
                self.error = f"Failed to established a new connection to {self.hostname}, type: {self.type}"

        except pexpect.EOF as err:
            self.error = f"Error connection to {self.hostname} [type: {self.type}]: {err}"
        except pexpect.TIMEOUT as err:
            self.error = f"Timeout connection to {self.hostname} [type: {self.type}]: {err}"
        except (pexpect.ExceptionPexpect, ExceptionPxssh) as err:
            self.error = f"Failed to established a new connection to {self.hostname} [type: {self.type}]: {err}"
        except BaseException as err:
            self.error = f"BaseException for {self.hostname}: {err}"
        finally:
            if self.error:
                self.connection = None
                logger.error(f'{self.error}')

    def command(self, cmd, eof_pattern=None, timeout=2) -> str or None:
        self.error = None
        if self.connection:
            try:
                self.connection.sendline(cmd)
                if eof_pattern:
                    self.connection.expect(eof_pattern, timeout=timeout)
                else:
                    self.connection.prompt()
                output = self.connection.before.decode('utf-8')
                # clear expect buffer after command
                if self.connection.before:
                    self.connection.expect(r'.+', timeout=0.2)
                    if self.connection.before:
                        logger.error(f'Error clearing buffer: {self.connection.before}\n')
                return output
            except pexpect.EOF as err:
                self.error = f"Error connection to {self.hostname} [type: {self.type}]: {err}"
            except pexpect.TIMEOUT as err:
                self.error = f"Timeout connection to {self.hostname} [type: {self.type}]: {err}"
            except (pexpect.ExceptionPexpect, BaseException) as err:
                self.error = f"BaseException for {self.hostname} [type: {self.type}]: {err}"
            finally:
                if self.error:
                    self.connection = None
                    logger.error(f'{self.error}')
                    return None


class SSHConnectionECI(SSHExpect):
    type = 'eci'
    promt = r"[>]"
    timeout = 2
    dev_mode = True

    def __init__(self, device: NetworkDevice):
        self.schema = device.schema
        super().__init__(device)

    @property
    def fetch(self):
        match self.schema:
            case 'dwdm_eci':
                return self._fetch_optics
            case _:
                raise ValueError(f'Schema {self.schema} is not supported')

    def _fetch_optics(self):
        commands_and_outputs = {'show chassis port oncp port-u0/1 | match "OTUA|Total power"': '',
                                'show chassis port oncp port-u0/2 | match "OTUA|Total power"': '',
                                'show chassis port oncp port-u1/1 | match "OTUA|Total power"': '',
                                'show chassis port oncp port-u1/2 | match "OTUA|Total power"': ''}
        device_data = []
        timestamp = int(time.time())

        for command in copy.deepcopy(commands_and_outputs):
            command_output = self.command(command, eof_pattern=[pexpect.EOF, pexpect.TIMEOUT], timeout=self.timeout)

            if command_output is not None:
                logger.debug(f'[ {self.hostname} ]  [ len: {len(command_output)} ]  \noutput: {command_output}\n')
                if len(command_output) < 100:
                    logger.info(f"{self.hostname} No data for command [{command}]. Continue to a next command")
                    continue

                if self.dev_mode:
                    loggerfile.debug(f'[ {self.hostname} ]  [ len: {len(command_output)} ]  \noutput: {command_output}\n')

                commands_and_outputs[command] = command_output
            else:
                logger.debug(f'{self.hostname} No fetching data')  # debug
                return {self.hostname: False}

        logger.debug(f"Buffer LEN: {len(commands_and_outputs)}")
        for cmd, output in commands_and_outputs.items():
            logger.debug(f"Command: {cmd}\nOutput: \n{output}\n")

        for cmd, output in commands_and_outputs.items():

            match = re.search(r'port-u(?P<amp_number>\d)/(?P<inout>\d)', cmd)
            inout_from_cmd = match.group('inout')
            match inout_from_cmd:
                case "1":
                    inout = 'IN'
                case "2":
                    inout = 'OUT'
                case _:
                    inout = None
            amp_number = match.group('amp_number')
            amplifier = f'OAu{amp_number}'
            if not (amp_number and inout):
                logger.error(f'{self.hostname} Error parsing command: {cmd}\n')
                return {self.hostname: False}

            lines = output.strip().split('\n')
            for line in lines:
                try:
                    line = re.sub(r'\x1B[@-_][0-?]*[ -/]*[@-~]', '', line)
                    line = re.sub(r'\s+', ' ', line)
                    line = line.strip()

                    if not line.startswith(('|', '+')):
                        continue

                    if self.dev_mode:
                        logger.debug(f'{self.hostname} cmd: {cmd}\nline: {line}\n')

                    if 'Total power' in line:
                        total_power = float(line.split(' ')[-2])

                        metric_total_power = GraphiteMetricECI(name=f"Total_Power_{inout}",
                                                               hostname=self.hostname,
                                                               value=total_power,
                                                               timestamp=timestamp,
                                                               amplifier=amplifier,
                                                               channel="sum")
                        logger.debug(f'{self.hostname} CREATE SUM METRIC: {metric_total_power}\n')
                        device_data.append(metric_total_power)
                        continue

                    column_values = re.split(r'\s+', line)
                    channel = column_values[1] if column_values[1].isdecimal() else None
                    value_power = float(column_values[5])
                    value_osnr = float(column_values[6])

                    name_power = f"Power_{inout}"
                    name_osnr = f"OSNR_{inout}"

                    metric_power = GraphiteMetricECI(name=name_power,
                                                     hostname=self.hostname,
                                                     value=value_power,
                                                     timestamp=timestamp,
                                                     amplifier=amplifier,
                                                     channel=channel)

                    metric_osnr = GraphiteMetricECI(name=name_osnr,
                                                    hostname=self.hostname,
                                                    value=value_osnr,
                                                    timestamp=timestamp,
                                                    amplifier=amplifier,
                                                    channel=channel)
                    if metric_power.is_valid(('amplifier', 'channel')):
                        logger.debug(f'{self.hostname} CREATE POWER METRIC: {metric_power}\n')
                        device_data.append(metric_power)
                        if self.dev_mode:
                            loggerfile.debug(f'{self.hostname} CREATE POWER METRIC: {metric_power}\n')
                    if metric_osnr.is_valid(('amplifier', 'channel')):
                        logger.debug(f'{self.hostname} CREATE OSNR METRIC: {metric_osnr}\n')
                        device_data.append(metric_osnr)
                        if self.dev_mode:
                            loggerfile.debug(f'{self.hostname} CREATE OSNR METRIC: {metric_osnr}\n')
                except ValueError:
                    logger.warning(f'{self.hostname} Metric parsing error in {line}')
        if device_data:
            metrics = convert_data_to_graphite_metrics(device_data)
            logger.debug(f'{self.hostname} Device metrics count: {len(metrics)}\n')
            Q.append(metrics)
            return {self.hostname: True}


class SSHConnectionJunos(SSHExpect):
    type = 'junos'
    promt = r"[>]"
    timeout = 2
    dev_mode = False

    def __init__(self, device: NetworkDevice):
        self.schema = device.schema
        super().__init__(device)

    @property
    def fetch(self):
        match self.schema:
            case 'spine_and_leaf':
                return self._fetch_fib
            case 'bct_v4':
                return self._fetch_bctv4
            case _:
                raise ValueError(f'Schema {self.schema} is not supported')

    def _fetch_bctv4(self):
        logger.info(f'{self.hostname} Running fetch for BCT-V4')
        pass

    def _fetch_fib(self):
        row_names = ('IPv4 Host', 'IPv4 LPM', 'IPv6 Host', 'IPv6 LPM(< 64)', 'IPv6 LPM(> 64)')
        cmd = 'show pfe route summary hw'
        fib_metric_name_percent = fib_metric_name_count = ''
        free_percent_column_index = -1
        used_column_index = -3
        type_column_index = 0
        device_data = []
        timestamp = int(time.time())

        output = self.command(cmd, eof_pattern=[pexpect.EOF, pexpect.TIMEOUT], timeout=self.timeout)

        if output is not None:
            logger.debug(f'[ {self.hostname} ]  [ len: {len(output)} ]  \noutput: {output}\n')
            if len(output) < 100:
                logger.info(f'{self.hostname} No data for command [{cmd}]. Continue...')
                return {self.hostname: False}
            lines = output.strip().split('\n')
            for line in lines:
                try:
                    # remove ansi escape code
                    # remove ansi escape codes and extra spaces
                    line = re.sub(r'\x1B[@-_][0-?]*[ -/]*[@-~]', '', line)
                    line_split = line.split(sep=2*' ')
                    column_values = list(filter(lambda l: l.strip(), line_split))

                    if not line.startswith('IP'):
                        continue

                    if len(column_values) > 1:
                        row_type_name = f'{column_values[type_column_index]}'
                        if row_type_name in row_names:
                            match row_type_name:
                                case 'IPv4 Host':
                                    fib_metric_name_percent = 'IPv4HostFree_percent'
                                    fib_metric_name_count = 'IPv4HostUsed_count'
                                case 'IPv4 LPM':
                                    fib_metric_name_percent = 'IPv4LpmFree_percent'
                                    fib_metric_name_count = 'IPv4LpmUsed_count'
                                case 'IPv6 Host':
                                    fib_metric_name_percent = 'IPv6HostFree_percent'
                                    fib_metric_name_count = 'IPv6HostUsed_count'
                                case 'IPv6 LPM(< 64)':
                                    fib_metric_name_percent = 'IPv6LpmLeEq64Free_percent'
                                    fib_metric_name_count = 'IPv6LpmLeEq64Used_count'
                                case 'IPv6 LPM(> 64)':
                                    fib_metric_name_percent = 'IPv6LpmGt64Free_percent'
                                    fib_metric_name_count = 'IPv6LpmGt64Used_count'

                            utilization_value_percent = int(float(column_values[free_percent_column_index].strip()))
                            utilization_value_count = int(column_values[used_column_index].strip())
                            metric_fib_percent = GraphiteMetricJunos(name=fib_metric_name_percent,
                                                                     hostname=self.hostname,
                                                                     value=utilization_value_percent,
                                                                     timestamp=timestamp)
                            metric_fib_count = GraphiteMetricJunos(name=fib_metric_name_count,
                                                                   hostname=self.hostname,
                                                                   value=utilization_value_count,
                                                                   timestamp=timestamp)
                            device_data.append(metric_fib_percent)
                            device_data.append(metric_fib_count)
                except ValueError:
                    logger.warning(f'{self.hostname} Metric parsing error in {line}')
        if device_data:
            metrics = convert_data_to_graphite_metrics(device_data)
            logger.debug(f'{self.hostname} Device metrics: {metrics}\n')
            Q.append(metrics)
            return {self.hostname: True}


class SSHConnectionFabric:
    @staticmethod
    def create_connection(device: NetworkDevice):
        ssh_classes = {'eci':   SSHConnectionECI,
                       'junos': SSHConnectionJunos}
        if device.device_type in ssh_classes:
            return ssh_classes[device.device_type](device)
        else:
            raise ValueError(f"Device type {device.device_type} is not supported")


class GraphiteMetric(ABC):
    @abstractmethod
    def is_valid(self, required: tuple):
        pass

    @abstractmethod
    def metric_path(self):
        pass


class GraphiteMetricECI(GraphiteMetric):
    amplifier: str
    channel: str

    def __init__(self, name, hostname, value, timestamp, **kwargs):
        self.name = name
        self.hostname = hostname
        self.value = value
        self.timestamp = timestamp

        for key, value in kwargs.items():
            self.__setattr__(key, value)

    def is_valid(self, required: tuple):
        for r in required:
            if r not in self.__dict__ or not self.__dict__.get(r):
                logger.warning(f'Metric {self.name} has not value {r}: {self.hostname}')
                return False
        return True

    def __str__(self):
        return f'{self.metric_path} == {self.value}'

    @property
    def metric_path(self):
        # graphite metric template: <hostname>.amplifier.<amplifier>.<channel>.<name>
        return f"{self.hostname}.amplifier.{self.amplifier}.{self.channel}.{self.name}"


class GraphiteMetricJunos:
    def __init__(self, hostname, name, value, timestamp):
        self.hostname = hostname
        self.name = name
        self.value = value
        self.timestamp = timestamp

    def is_valid(self, required: tuple, hostname: str):
        pass

    def __str__(self):
        return f'{self.metric_path} == {self.value}'

    @property
    def metric_path(self):
        # graphite metric template: <hostname>.system.<name>
        return f"{self.hostname}.system.{self.name}"


class GraphiteClient:
    def __init__(self, host, port, prefix=None, dryrun=False):
        self.dryrun = dryrun
        graphyte.init(host, port=port, prefix=prefix)

    def send_metric(self, metric, value, timestamp=None):
        if timestamp is None:
            timestamp = int(time.time())
        if not self.dryrun:
            graphyte.send(metric, value, timestamp)

    def send_metrics(self, metrics: list[tuple]):
        for item in metrics:
            self.send_metric(metric=item[0], value=item[1], timestamp=item[2])


def convert_data_to_graphite_metrics(data: list) -> list[tuple]:
    metrics = []
    for d in data:
        metrics.append((d.metric_path, d.value, d.timestamp))
    return metrics


def fetch_data_by_cli(device_object: NetworkDevice) -> dict:
    hostname = device_object.hostname
    logger.info(f'Fetching data from {hostname} ...')

    with SSHConnectionFabric.create_connection(device=device_object) as ssh:
        if not ssh.connection:
            return {hostname: False}
        try:
            ssh.fetch()
        except IndexError as err:
            logger.error(f'Error while fetching data from {hostname}...: {err}')
            return {hostname: False}
        return {hostname: True}


def push_to_graphite(message: str) -> bool:
    logger.info(message)
    if Q:
        while Q:
            metrics = Q.popleft()
            Graphite.send_metrics(metrics)
            logger.debug(f'Metrics pushed to Graphite: {metrics}\n',)
    else:
        logger.info('No data to pushing...')
        return False
    return True


class Schema:
    def __init__(self, name, query, device_os, username, password, ssh_key, hostnames=None, hostnames_ignore=None, fetch_interval=None, push_interval=None):
        self.use_cmdb = True
        self.name = name
        self.query = query
        self.device_os = device_os
        self.username = username
        self.password = password
        self.ssh_key = ssh_key
        self.push_interval = push_interval
        self.fetch_interval = fetch_interval
        self.hostnames_ignore = hostnames_ignore
        if hostnames:
            self.hostnames = hostnames
            self.use_cmdb = False

    def __str__(self):
        return f'{self.name} {self.device_os} {self.username} {self.password} {self.query}'

    def set_devices(self, values: list):
        self.hostnames = values

    def show_stats(self, check_connections=True):
        current_jobs = schedule.get_jobs()
        for job in current_jobs:
            print(f'JOB: {job.__str__}')
        logger.info(f'Schema: {self.name}')
        logger.info(f'Timers: {self.push_interval} :: {self.fetch_interval}')
        logger.info(f'Devices [={len(self.hostnames)}]: {self.hostnames}')
        if self.use_cmdb:
            logger.info(f'CMDB Query: {self.query}')


def get_devices(schema: Schema, cmdb_filename: str):
    devices = []
    global DEVICES_IN_CMDB

    if schema.use_cmdb:
        cmdb_query = CMDBQuery(
            'NetworkHostListWithIP',
            ('HostName', 'NetworkRoles'),
            'SELECT * FROM',
            f"{schema.query}"
            " GROUP BY HostName"
        )
        hostnames = read_cmdb(cmdb_filename, cmdb_query)
        if schema.hostnames_ignore:
            hostnames = list(filter(lambda x: x not in schema.hostnames_ignore, hostnames))
        schema.set_devices(hostnames)

    for hostname in schema.hostnames:
        devices.append(NetworkDevice(hostname=hostname,
                                     device_type=schema.device_os,
                                     username=schema.username,
                                     password=schema.password,
                                     ssh_key=schema.ssh_key,
                                     schema=schema.name))
    DEVICES_IN_CMDB[schema.name] = devices
    return devices


def parse_schemas():
    config_schemas = CONFIG['schemas']
    schemas = []
    for cfg_schema in config_schemas:
        for schema_name, schema_data in cfg_schema.items():
            name = schema_name
            device_os = schema_data.get('os', None)
            username = schema_data.get('username', None)
            password = schema_data.get('password', None)
            ssh_key = schema_data.get('ssh_key', None)
            hostnames = schema_data.get('hostnames', None)
            hostnames_ignore = schema_data.get('hostnames_ignore', None)
            if hostnames and hostnames_ignore:
                hostnames = list(filter(lambda x: x not in hostnames_ignore, hostnames))
            query = schema_data.get('query', None)
            fetch_interval = schema_data.get('fetch_interval', None)
            push_interval = schema_data.get('push_interval', None)

            if all((device_os,
                    username,
                    bool(password) | bool(ssh_key),
                    bool(query) | bool(hostnames))):
                schema = Schema(name=name,
                                device_os=device_os,
                                username=username,
                                password=password,
                                ssh_key=ssh_key,
                                hostnames=hostnames,
                                fetch_interval=fetch_interval or CONFIG['global']['fetch_interval'],
                                push_interval=push_interval or CONFIG['global']['push_interval'],
                                hostnames_ignore=hostnames_ignore,
                                query=query,
                                )
                schemas.append(schema)
    return schemas


def start_fetching(message: str = None, devices=None, dry_run=False):
    logger.info(message)  # debug
    if dry_run:
        return False
    with ThreadPoolExecutor() as executor:
        fetch_result = executor.map(fetch_data_by_cli, devices)
    fetch_result_list = list(fetch_result)
    result = {k: v for d in fetch_result_list for k, v in d.items()}
    failed_devices = [key for key, value in result.items() if value is False]
    if failed_devices:
        logger.warning(f'Failed devices: {", ".join(failed_devices)}')
    return True


def read_cmdb(db_filename: str, table: CMDBQuery):
    """
    get data from CMDB filename

    :param table: CMDB table object
    :param db_filename: CMDB filename
    """
    query = f'{table.query} {table.name} {table.params}'
    keys = table.keys
    hosts = []
    db_filename_tmp = db_filename + '.tmp'
    try:
        if copyfile(db_filename, db_filename_tmp):
            with sqlite3.connect(db_filename_tmp) as conn:
                cmdb_data = conn.execute(query).fetchall()

            for row in cmdb_data:
                hostname = row[keys.index('HostName')]
                # remove symbol '_' from the HostName of stack devices
                hostname = hostname.split('_')[0] if '_' in hostname else hostname
                # remove duplicates
                if hostname in hosts:
                    continue
                hosts.append(hostname)
            return hosts
    except Exception as err:
        text = f'ERROR: {read_cmdb.__name__}: some issue with connection to filename {db_filename}'
        raise Exception(text) from err


def read_config(filename):
    required_options = ('global', 'cmdb', 'graphite', 'schemas')
    try:
        with open(filename, 'r') as f:
            cfg = yaml.safe_load(f)
    except FileNotFoundError:
        logger.error(f'File {filename} not found!')
        sys.exit(1)
    except yaml.YAMLError:
        logger.error(f'File {filename} has not valid YAML format!')
        sys.exit(1)
    if not cfg:
        logger.error('No config in file!')
        sys.exit(1)
    else:
        for option in required_options:
            if option not in cfg:
                logger.error(f'No {option} config!')
                sys.exit(1)
        for schema_dict in cfg['schemas']:
            for schema_name, schema_data in schema_dict.items():
                if 'username' not in schema_data:
                    logger.error(f'No username configured for {schema_name}!')
                    sys.exit(1)
                if 'os' not in schema_data:
                    logger.error(f'No device_os configured for {schema_name}!')
                    sys.exit(1)
                if 'username' not in schema_data:
                    logger.error(f'No username configured for {schema_name}!')
                    sys.exit(1)
                if 'password' not in schema_data and 'ssh_key' not in schema_data:
                    logger.error(f'No password/key configured for {schema_name}!')
                    sys.exit(1)
    return cfg


def end_script():
    if schedule.jobs:
        schedule.clear()
    Connections.close_all_connections()
    logger.info('Clear all schedule tasks!')
    logger.info('Closed all ssh connections!')
    sys.exit(1)


def main():
    global DEVICES_IN_CMDB
    hostnames_hash_old = {}

    sleep_interval_global = CONFIG['global']['sleep_interval']
    cmdb_filename = CONFIG['cmdb']['filename']
    cmdb_fresh = CONFIG['cmdb']['fresh_interval_min']

    cmdb_created_time = os.stat(cmdb_filename)
    delta = int((datetime.now() - datetime.fromtimestamp(cmdb_created_time.st_mtime)).seconds // 60)
    if delta > int(cmdb_fresh):
        logger.warning('!!! Pay attention: CMDB filename is very old !!!')

    schemas = parse_schemas()

    if not schemas:
        logger.error('Not found any schema in config!')
        sys.exit(1)

    for schema in schemas:
        get_devices(schema, cmdb_filename)
        schedule.every(cmdb_fresh//2).minutes.do(get_devices,
                                                 schema,
                                                 cmdb_filename).tag('get_devices')
        schedule.every(schema.push_interval).seconds.do(push_to_graphite,
                                                        message='Pushing all metrics to Graphite ...').tag(f'push_to_graphite_{schema.name}')
        schedule.every(schema.push_interval).seconds.do(schema.show_stats).tag(f'show_stats_{schema.name}')
        schedule.every(120).minutes.do(Connections.close_all_connections)
        logger.info(f'\nSchema found: {schema.name}')
        schema.show_stats(check_connections=False)

    while 1:
        schedule.run_pending()

        for schema in schemas:
            hostnames_hash_template = str(list((d.hostname for d in DEVICES_IN_CMDB[schema.name])))
            hostnames_hash_now = hashlib.sha256(hostnames_hash_template.encode('utf-8')).hexdigest()
            if hostnames_hash_old.get(schema.name) != hostnames_hash_now:
                hostnames_hash_old[schema.name] = hostnames_hash_now
                # if device's list changed - renew fetching job
                schedule.clear(tag=f'start_fetching_{schema.name}')
                schedule.every(schema.fetch_interval).seconds.do(start_fetching,
                                                                 message='Start fetching metrics ...',
                                                                 devices=DEVICES_IN_CMDB[schema.name]).tag(f'start_fetching_{schema.name}')
        time.sleep(sleep_interval_global)


if __name__ == '__main__':
    # ARGS section
    parser = argparse.ArgumentParser(description="cli_to_graphite")
    parser.add_argument('-config', '--CONFIG_FILE',
                        type=str, required=False,
                        default=f"{CONFIG_FILE}",
                        help="config filename")
    parser.add_argument('-dryrun', '--DRYRUN',
                        type=bool, required=False,
                        default=False,
                        help="dryrun mode")
    running_args = parser.parse_args()

    CONFIG = read_config(f'/config/{running_args.CONFIG_FILE}')
    level = CONFIG['global']['logging']
    # running_args.DRYRUN = True  ### run as dry for debug
    LoguruLogger.remove()
    logger = copy.deepcopy(LoguruLogger)
    loggerfile = copy.deepcopy(LoguruLogger)

    logger.add(sink=sys.stdout,
               level=level,
               enqueue=True,
               format="<cyan>{time:YYYY-MM-DD HH:mm:ss}</cyan> >>> "
                      "<level>{level}</level> "
                      "<bold>{message}</bold>")

    loggerfile.add(sink=f'logs/cli_to_graphite.log',
                   level=level,
                   rotation="00:00",
                   retention="7 days",
                   compression="gz",
                   enqueue=True,
                   format="{time:YYYY-MM-DD HH:mm} >>> "
                          "{level} "
                          "{message}"
                   )

    logger.info('Start cli_to_graphite script...')
    Q = MutexDeque()
    Connections = NetworkConnections()
    Graphite = GraphiteClient(host=CONFIG['graphite']['url'],
                              port=CONFIG['graphite']['port'] if 'port' in CONFIG['graphite'] else '2003',
                              prefix=CONFIG['graphite']['prefix'] if 'prefix' in CONFIG['graphite'] else None,
                              dryrun=(CONFIG['graphite']['mode'] == 'dev'))
    try:
        main()
    except BaseException as e:
        logger.error(e)
        traceback.print_exc()
        end_script()
