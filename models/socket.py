import os
import simsym
import symtypes
import errno
import model
import signal
#import fs_testgen

AF_INET = 2
AF_INET6 = 10
SOCK_DGRAM = 2
SHUT_RD = 0
SHUT_WR = 1
SHUT_RDWR = 2

SDataVal = simsym.tuninterpreted("SDataVal")

DATAVAL_BYTES = 4096
PAGE_BYTES = 4096
PAGE_DATAVALS = PAGE_BYTES / DATAVAL_BYTES
assert PAGE_BYTES % DATAVAL_BYTES == 0
DATA_MAX_LEN = 8

SPid = simsym.SBool # TODO: bool ???
SOffset = simsym.tsynonym("SOffset", simsym.SInt)
SAddr = simsym.tsynonym("SAddr", simsym.SInt)
SPort = simsym.tsynonym("SPort", simsym.SInt)
SData = symtypes.tsmalllist(DATA_MAX_LEN, SDataVal, lenType=SOffset)
SBuffer = simsym.tstruct(data = SData)
SBindRecord = symtypes.tdict(SPort, symtypes.tdict(SPid, simsym.SBool))

class SFd(simsym.tstruct(domain = simsym.SInt,
                         type = simsym.SInt,
                         prot = simsym.SInt,
                         can_read = simsym.SBool,
                         can_write = simsym.SBool,
                         is_bound = simsym.SBool,
                         is_connected = simsym.SBool,
                         local_addr = SAddr,
                         local_port = SPort,
                         remote_addr = SAddr,
                         remote_port = SPort,
                         send_buffer = SBuffer,
                         recv_buffer = SBuffer)):
    def _declare_assumptions(self, assume):
        super(SFd, self)._declare_assumptions(assume)
        assume(self.domain == AF_INET or self.domain == AF_INET6)
        assume(self.type == SOCK_DGRAM)
        assume(self.prot == 0)

    #def _eq_internal(self, o):
    #    if type(self) != type(o):
    #        return NotImplemented
    #    return True

SFdNum = simsym.tsynonym("SFdNum", simsym.SInt)
SFdMap = symtypes.tdict(SFdNum, SFd)
SProc = symtypes.tstruct(fd_map = SFdMap)
STime = simsym.tsynonym("STime", simsym.SInt)

class Socket(simsym.tstruct(
        # Process state
        proc0=SProc, proc1=SProc,
        # Bind records
        bind_rec=SBindRecord)):

    def getproc(self, pid):
        if pid == False:
            return self.proc0
        return self.proc1

    def add_selfpid(self, pid):
        ## XXX hack due to our simplified PID model
        ## without loss of generality, assume syscall "a" happens in proc0
        if str(pid).startswith('a.'):
            simsym.assume(pid == False)

    def enqueue_buffer(self, buffer, databyte):
        simsym.assume(buffer.data.len() < DATA_MAX_LEN)
        buffer.data.append(databyte)
    
    def dequeue_buffer(self, buffer):
        d = buffer.data[0]
        buffer.data.shift()
        return d

    def is_bound(self, port, pid):
        if not self.bind_rec.contains(port):
            return False
        if not self.bind_rec[port].contains(pid):
            return False
        return self.bind_rec[port][pid]

    def set_bound(self, port, pid):
        if not self.bind_rec.contains(port):
            self.bind_rec.create(port)
        if not self.bind_rec[port].contains(pid):
            self.bind_rec[port].create(pid)
        self.bind_rec[port][pid] = True

    def unset_bound(self, port, pid):
        if not self.bind_rec.contains(port):
            return
        if not self.bind_rec[port].contains(pid):
            return
        self.bind_rec[port][pid] = False

    # transport layer
    def read_transport(self, sock):
        if sock.recv_buffer.data.len() > 0:
            d = self.dequeue_buffer(sock.recv_buffer)
            return {'r': DATAVAL_BYTES, 'data': d}
        else:
            return {'r': 0}

    # transport layer
    def write_transport(self, sock, databyte):
        self.enqueue_buffer(sock.send_buffer, databyte)
        return {'r': DATAVAL_BYTES}

    # network layer
    def read_net(self, sock):
      return {'r': DATAVAL_BYTES, 'data': '???'}

    # network layer
    def write_net(self, sock, databyte):
      return {'r': DATAVAL_BYTES}

    # datalink layer
    def read_datalink(self, sock):
      return {'r': DATAVAL_BYTES, 'data': '???'}

    # not a system call
    @model.methodwrap(from_addr=SAddr,
                      from_port=SPort,
                      to_addr=SAddr,
                      to_port=SPort,
                      pid=SPid)
    def on_delivery(self, from_addr, from_port, to_addr, to_port, pid):
        self.add_selfpid(pid)
        for rpid in [False, True]:
            if self.is_bound(to_port, rpid):
                # TODO
                pass
        return {'r': 0}

    @model.methodwrap(domain=simsym.SInt,
                      type=simsym.SInt,
                      prot=simsym.SInt,
                      anyfd=simsym.SBool,
                      pid=SPid,
                     )
    def socket(self, domain, type, prot, anyfd, pid):
        self.add_selfpid(pid)
        
        if not ((domain == AF_INET or domain == AF_INET6)
                and type == SOCK_DGRAM and prot == 0):
          return {'r': -1, 'errno': errno.EAFNOSUPPORT}
        
        internal_ret_fd = SFdNum.var('internal_ret_fd*')
        simsym.assume(internal_ret_fd >= 0)
        simsym.assume(simsym.symnot(self.getproc(pid).fd_map.contains(internal_ret_fd)))

        ## Lowest FD
        otherfd = SFdNum.var('fd')
        simsym.assume(simsym.symor([anyfd,
            simsym.symnot(simsym.exists(otherfd,
                simsym.symand([otherfd >= 0,
                               otherfd < internal_ret_fd,
                               self.getproc(pid).fd_map.contains(otherfd)])))]))

        sock = self.getproc(pid).fd_map.create(internal_ret_fd)
        sock.domain = domain
        sock.type = type
        sock.prot = prot
        sock.can_read = True
        sock.can_write = True
        sock.is_bound = False
        sock.is_connected = False
        sock.local_addr = 0
        sock.local_port = 0
        sock.remote_addr = 0
        sock.remote_port = 0

        return {'r': internal_ret_fd}

    @model.methodwrap(fd=SFdNum, pid=SPid)
    def read(self, fd, pid):
        self.add_selfpid(pid)
        if not self.getproc(pid).fd_map.contains(fd):
            return {'r': -1, 'errno': errno.EBADF}
        sock = self.getproc(pid).fd_map[fd]
        if not sock.can_read:
            return {'r': 0}
        if not sock.is_bound or not sock.is_connected:
            return {'r': -1, 'errno': errno.ENOTCONN}
        return self.read_transport(sock)

    @model.methodwrap(fd=SFdNum, databyte=SDataVal, pid=SPid)
    def write(self, fd, databyte, pid):
        self.add_selfpid(pid)
        if not self.getproc(pid).fd_map.contains(fd):
            return {'r': -1, 'errno': errno.EBADF}
        sock = self.getproc(pid).fd_map[fd]
        if not sock.can_write:
            # TODO: signal
            return {'r': 0}
        if not sock.is_bound or not sock.is_connected:
            return {'r': -1, 'errno': errno.ENOTCONN}
        return self.write_transport(sock, databyte)

    @model.methodwrap(fd=SFdNum, addr=SAddr, port=simsym.SInt, pid=SPid)
    def connect(self, fd, addr, port, pid):
        self.add_selfpid(pid)
        if not self.getproc(pid).fd_map.contains(fd):
            return {'r': -1, 'errno': errno.EBADF}
        sock = self.getproc(pid).fd_map[fd]
        if sock.is_connected:
            return {'r': -1, 'errno': errno.EISCONN}
        sock.is_connected = True
        sock.remote_addr = addr
        sock.remote_port = port
        # TODO: register?
        return {'r': 0}

    @model.methodwrap(fd=SFdNum, addr=SAddr, port=simsym.SInt, pid=SPid)
    def bind_(self, fd, addr, port, pid):
        self.add_selfpid(pid)
        if not self.getproc(pid).fd_map.contains(fd):
            return {'r': -1, 'errno': errno.EBADF}
        sock = self.getproc(pid).fd_map[fd]
        if sock.is_bound:
            return {'r': -1, 'errno': errno.EINVAL}
        sock.is_bound = True
        sock.local_addr = addr
        sock.local_port = port
        self.set_bound(port, pid)
        return {'r': 0}

    @model.methodwrap(fd=SFdNum, backlog=simsym.SInt, pid=SPid)
    def listen(self, fd, backlog, pid):
        self.add_selfpid(pid)
        if not self.getproc(pid).fd_map.contains(fd):
            return {'r': -1, 'errno': errno.EBADF}
        sock = self.getproc(pid).fd_map[fd]
        return {'r': -1, 'errno': errno.EOPNOTSUPP}

    @model.methodwrap(fd=SFdNum, pid=SPid)
    def accept(self, fd, pid):
        self.add_selfpid(pid)
        if not self.getproc(pid).fd_map.contains(fd):
            return {'r': -1, 'errno': errno.EBADF}
        sock = self.getproc(pid).fd_map[fd]
        return {'r': -1, 'errno': errno.EOPNOTSUPP}

    @model.methodwrap(fd=SFdNum, how=simsym.SInt, pid=SPid)
    def shutdown(self, fd, how, pid):
        self.add_selfpid(pid)
        if not self.getproc(pid).fd_map.contains(fd):
            return {'r': -1, 'errno': errno.EBADF}
        sock = self.getproc(pid).fd_map[fd]
        if how == SHUT_RD or how == SHUT_RDWR:
            sock.can_read = False
        if how == SHUT_WR or how == SHUT_RDWR:
            sock.can_write = False
        return {'r': 0}

    @model.methodwrap(fd=SFdNum, pid=SPid)
    def close(self, fd, pid):
        self.add_selfpid(pid)
        if not self.getproc(pid).fd_map.contains(fd):
            return {'r': -1, 'errno': errno.EBADF}
        sock = self.getproc(pid).fd_map[fd]
        if sock.is_connected:
            # TODO: unconnect
            sock.is_connected = False
        if sock.is_bound:
            sock.is_bound = False
            self.unset_bound(sock.local_port, pid)
        del self.getproc(pid).fd_map[fd]
        return {'r': 0}

model_class = Socket
#model_testgen = fs_testgen.FsTestGenerator
