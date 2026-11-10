"""Unpack the bounded boat log's goal archive for standalone grow replay."""
import base64, io, pathlib, sys, tarfile
log = pathlib.Path(sys.argv[1]).read_text()
archive = base64.b64decode(log.split('\nGOALS_ARCHIVE\n', 1)[1].splitlines()[0])
dest = pathlib.Path(sys.argv[2]); dest.mkdir(parents=True, exist_ok=True)
with tarfile.open(fileobj=io.BytesIO(archive), mode='r:xz') as tf:
    for member in tf:
        if member.isfile() and member.name.removeprefix('./').isdigit():
            raise ValueError('goal should have a json extension')
        name = pathlib.PurePosixPath(member.name).name
        if member.isfile() and name.endswith('.json'):
            (dest / name).write_bytes(tf.extractfile(member).read())
