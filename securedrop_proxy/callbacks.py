import subprocess
import sys
import json
import uuid


def err_on_done(res):
    print(json.dumps(res.__dict__))
    sys.exit(1)

# callback for handling non-JSON content. in production-like
# environments, we want to call `qvm-move-to-vm` (and expressly not
# `qvm-move`, since we want to include the destination VM name) to
# move the content to the target VM. for development and testing, we
# keep the file on the local VM.
#
# In any case, this callback mutates the given result object (in
# `res`) to include the name of the new file, or to indicate errors.
def on_save(fh, res, conf):
    fn = str(uuid.uuid4())

    try:
        subprocess.run(["cp", fh.name, "/tmp/{}".format(fn)])
        if conf.dev is not True:
            subprocess.run(['qvm-move-to-vm', conf.target_vm, "/tmp/{}".format(fn)])
    except Exception:
        res.status = 500
        res.headers['Content-Type'] = 'application/json'
        res.headers['X-Origin-Content-Type'] = res.headers['Content-Type']
        res.body = json.dumps({"error": "Unhandled error while handling non-JSON content, sorry"})
        return

    res.headers['Content-Type'] = 'application/json'
    res.headers['X-Origin-Content-Type'] = res.headers['Content-Type']
    res.body = json.dumps({'filename': fn })


def on_done(res):
    print(json.dumps(res.__dict__))
