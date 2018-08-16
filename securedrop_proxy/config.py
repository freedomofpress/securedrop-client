import os
import yaml

class Conf:
    scheme = ''
    host = ''
    port = 0
    dev = False

def read_conf(conf_path, p):

    if not os.path.isfile(conf_path):
        p.simple_error(500, 'Configuration file does not exist at {}'.format(conf_path))
        p.on_done(p.res)

    try:
        fh = open(conf_path, 'r')
        conf_in = yaml.load(fh)
    except yaml.YAMLError:
        p.simple_error(500, 'YAML syntax error while reading configuration file {}'.format(conf_path))
        p.on_done(p.res)
    except Exception:
        p.simple_error(500, 'Error while opening or reading configuration file {}'.format(conf_path))
        p.on_done(p.res)

    req_conf_keys = set(('host','scheme','port'))
    missing_keys = req_conf_keys - set(conf_in.keys())
    if len(missing_keys) > 0:
        p.simple_error(500, 'Configuration file missing required keys: {}'.format(missing_keys))
        p.on_done(p.res)

    c = Conf()
    c.host = conf_in['host']
    c.scheme = conf_in['scheme']
    c.port = conf_in['port']

    if 'dev' in conf_in and conf_in['dev'] is True:
        c.dev = True
    else:
        if 'target_vm' not in conf_in:
            p.simple_error(500, 'Configuration file missing `target_vm` key, which is required when not in development mode')
            p.on_done(p.res)

        c.target_vm = conf_in['target_vm']

    return c
