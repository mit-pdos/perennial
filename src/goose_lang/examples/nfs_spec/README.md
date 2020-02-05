## NSF SERVER/CLIENT SETUP

Add to `/etc/exports`: 
```/ localhost(rw,sync,insecure,no_root_squash)```

Run an NFS server on Ubuntu:

```
sudo apt install nfs-kernel-server
sudo apt install nfs-common // for client
systemctl start nfs-server
```

Create an nfs trace to analyze with our NFS spec (requires sudo): 
```
mount localhost:/ /mnt/x -o vers=3
tcpdump -w /tmp/nfs.pcap -s 1600 -i lo port 2049
(ls -ld /proc/self/fd/5; ls -ld /proc/self/fd/5) 5< /mnt/x/etc/timezone
```

## Run the Symbolic NFS3API Interpreter 
Install python packages (via pip for python2):
    * z3-solver==4.8.7
    * dpkt

Run the Coq/Gallina spec in `NFS3API.v`
to extract to `NFS3API.json`

Extract to z3 expressions and solve for valid trace responses (requires that an nfs trace is in /tmp/nfs.pcap): `python symrun.py`
