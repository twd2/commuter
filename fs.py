import z3
import simsym
import symtypes
import errno
import model

class SFn(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('Fn')

class SInum(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('Inum')

class SDataByte(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('DataByte')

class SPid(simsym.SExpr, simsym.SymbolicConst):
    __z3_sort__ = z3.DeclareSort('Pid')

SData = symtypes.tlist(SDataByte)
SFd = simsym.tstruct(inum = SInum, off = simsym.SInt)
SFdMap = symtypes.tdict(simsym.SInt, SFd)
SProc = symtypes.tstruct(fd_map = SFdMap)
SProcMap = symtypes.tdict(SPid, SProc)
SDirMap = symtypes.tdict(SFn, SInum)
SInode = simsym.tstruct(data = SData,
                        nlink = simsym.SInt,
                        ## XXX Directories impl:
                        # isdir = simsym.SBool,
                        # dirmap = SDirMap,
                       )
SIMap = symtypes.tmap(SInum, SInode)
## XXX Directories impl:
# SPathname = simsym.tstruct(last = SFn)
## XXX Non-directories impl:
SPathname = SFn

## Although some things are integers, we treat them as uninterpreted
## sorts in IsomorphicMatch, by checking what decl the integer is
## being assigned to.  The first part of the tuple is the decl, and
## the second is the fake uninterpreted sort name that these values
## will be treated as.  The sort name only matters for matching up
## with other sort names in this same list.  This results in an
## approximation; see also the comment about else clause handling
## in IsomorphicMatch.

pseudo_sort_decls = [
    (SInode.__z3_sort__.nlink, 'file-nlink'),
    (SData.__z3_sort__._len, 'file-length'),
]

## Ignore some pseudo sort names altogether when enumerating models.

pseudo_sort_ignore = {
    'file-nlink': True,     ## unused for test generation
    'file-length': True,    ## too many cases in link*link
    'fd-num': False,
}

def add_pseudo_sort_decl(decl, name):
    for d, _ in pseudo_sort_decls:
        if d.eq(decl): return
    pseudo_sort_decls.append((decl, name))

class Fs(model.Struct):
    __slots__ = ['i_map',
                 'pid_map',

                 ## XXX Non-directories impl:
                 'root_dir',
                ]
    root_inum = SInum.any('Inum.root')

    def __init__(self):
        self.i_map = SIMap.any('Fs.imap')
        self.pid_map = SProcMap.any('Fs.pidmap')

        ## XXX Non-directories impl:
        self.root_dir = SDirMap.any('Fs.rootdir')

    def iused(self, inum):
        dir = SInum.any('dir')
        fn = SFn.any('fn')
        fd = simsym.SInt.any('fd')
        pid = SPid.any('pid')

        # If we try to simply index into dirmap, its __getitem__
        # won't have access to the supposition that it contains the right
        # key, and throw an exception.  Thus, we use _map directly.
        return simsym.symor([
            ## XXX Directories impl:
            # simsym.exists(dir,
            #     simsym.symand([
            #         self.i_map[dir].isdir,
            #         simsym.exists(fn,
            #             simsym.symand([self.i_map[dir].dirmap.contains(fn),
            #                            self.i_map[dir].dirmap._map[fn] == inum]))])),

            ## XXX Non-directories impl:
            simsym.exists(fn,
                simsym.symand([self.root_dir.contains(fn),
                               self.root_dir._map[fn] == inum])),

            simsym.exists((fd, pid),
                simsym.symand([self.pid_map.contains(pid),
                               self.pid_map._map[pid].fd_map.contains(fd),
                               self.pid_map._map[pid].fd_map._map[fd].inum == inum]))])

    def add_fdvar(self, fdvar):
        add_pseudo_sort_decl(simsym.unwrap(fdvar).decl(), 'fd-num')

    def add_offvar(self, offvar):
        add_pseudo_sort_decl(simsym.unwrap(offvar).decl(), 'file-length')

    def nameiparent(self, pn):
        ## XXX Non-directories impl:
        return 0, self.root_dir, pn

        ## XXX Directories impl:
        # simsym.assume(self.i_map[self.root_inum].isdir)
        # return self.root_inum, self.i_map[self.root_inum].dirmap, pn.last

    def sympid(self, name):
        pid = SPid.any(name)
        simsym.assume(self.pid_map.contains(pid))
        return pid

    def open(self, which):
        pid = self.sympid('Fs.open[%s].pid' % which)
        pn = SPathname.any('Fs.open[%s].pn' % which)
        creat = simsym.SBool.any('Fs.open[%s].creat' % which)
        excl = simsym.SBool.any('Fs.open[%s].excl' % which)
        trunc = simsym.SBool.any('Fs.open[%s].trunc' % which)
        # anyfd = simsym.SBool.any('Fs.open[%s].anyfd' % which)
        anyfd = False
        _, pndirmap, pnlast = self.nameiparent(pn)
        if creat:
            if not pndirmap.contains(pnlast):
                inum = SInum.any('Fs.open[%s].ialloc' % which)
                simsym.add_internal(inum)
                simsym.assume(simsym.symnot(self.iused(inum)))

                data_empty = SData.any('Data.empty')
                simsym.assume(data_empty._len == 0)
                idata = SInode.any()
                idata.data = data_empty
                idata.nlink = 1
                self.i_map[inum] = idata
                pndirmap[pnlast] = inum
            else:
                if excl: return ('err', errno.EEXIST)
        if not pndirmap.contains(pnlast):
            return ('err', errno.ENOENT)
        if trunc:
            data_empty = SData.any('Data.empty')
            simsym.assume(data_empty._len == 0)
            self.i_map[pndirmap[pnlast]].data = data_empty

        fd = simsym.SInt.any('Fs.open[%s].fd' % which)
        self.add_fdvar(fd)
        simsym.add_internal(fd)
        simsym.assume(fd >= 0)
        simsym.assume(simsym.symnot(self.pid_map[pid].fd_map.contains(fd)))

        ## Lowest FD
        otherfd = simsym.SInt.any('fd')
        simsym.assume(simsym.symor([anyfd,
            simsym.symnot(simsym.exists(otherfd,
                simsym.symand([otherfd >= 0,
                               otherfd < fd,
                               self.pid_map[pid].fd_map.contains(otherfd)])))]))

        fd_data = SFd.any()
        fd_data.inum = pndirmap[pnlast]
        fd_data.off = 0
        self.pid_map[pid].fd_map[fd] = fd_data

        return ('ok', fd)

    def rename(self, which):
        src = SPathname.any('Fs.rename[%s].src' % which)
        dst = SPathname.any('Fs.rename[%s].dst' % which)
        srcdiri, srcdirmap, srclast = self.nameiparent(src)
        dstdiri, dstdirmap, dstlast = self.nameiparent(dst)
        if not srcdirmap.contains(srclast):
            return ('err', errno.ENOENT)
        if srcdiri == dstdiri and srclast == dstlast:
            return ('ok',)
        if dstdirmap.contains(dstlast):
            dstinum = dstdirmap[dstlast]
        else:
            dstinum = None
        dstdirmap[dstlast] = srcdirmap[srclast]
        del srcdirmap[srclast]
        if dstinum is not None:
            self.i_map[dstinum].nlink = self.i_map[dstinum].nlink - 1
        return ('ok',)

    def unlink(self, which):
        pn = SPathname.any('Fs.unlink[%s].pn' % which)
        _, dirmap, pnlast = self.nameiparent(pn)
        if not dirmap.contains(pnlast):
            return ('err', errno.ENOENT)
        inum = dirmap[pnlast]
        del dirmap[pnlast]
        self.i_map[inum].nlink = self.i_map[inum].nlink - 1
        return ('ok',)

    def link(self, which):
        oldpn = SPathname.any('Fs.link[%s].old' % which)
        newpn = SPathname.any('Fs.link[%s].new' % which)
        olddiri, olddirmap, oldlast = self.nameiparent(oldpn)
        newdiri, newdirmap, newlast = self.nameiparent(newpn)
        if not olddirmap.contains(oldlast):
            return ('err', errno.ENOENT)
        if newdirmap.contains(newlast):
            return ('err', errno.EEXIST)
        inum = olddirmap[oldlast]
        newdirmap[newlast] = inum
        self.i_map[inum].nlink = self.i_map[inum].nlink + 1
        return ('ok',)

    def iread(self, inum, off):
        simsym.assume(off >= 0)
        if off >= self.i_map[inum].data._len:
            return ('eof',)
        return ('data', self.i_map[inum].data[off])

    def read(self, which):
        pid = self.sympid('Fs.read[%s].pid' % which)
        fd = simsym.SInt.any('Fs.read[%s].fd' % which)
        self.add_fdvar(fd)
        if not self.pid_map[pid].fd_map.contains(fd):
            return ('err', errno.EBADF)
        off = self.pid_map[pid].fd_map[fd].off
        r = self.iread(self.pid_map[pid].fd_map[fd].inum, off)
        if r[0] == 'data':
            self.pid_map[pid].fd_map[fd].off = off + 1
        return r

    def pread(self, which):
        pid = self.sympid('Fs.pread[%s].pid' % which)
        fd = simsym.SInt.any('Fs.pread[%s].fd' % which)
        self.add_fdvar(fd)
        off = simsym.SInt.any('Fs.pread[%s].off' % which)
        self.add_offvar(off)
        if not self.pid_map[pid].fd_map.contains(fd):
            return ('err', errno.EBADF)
        return self.iread(self.pid_map[pid].fd_map[fd].inum, off)

    def iwrite(self, inum, off, databyte):
        simsym.assume(off >= 0)
        ## Avoid overly-long files.  fs-test.py caps file size at 16 units.
        simsym.assume(off < 10)
        ## XXX Handle sparse files?
        simsym.assume(off <= self.i_map[inum].data._len)

        if off == self.i_map[inum].data._len:
            self.i_map[inum].data.append(databyte)
        else:
            self.i_map[inum].data[off] = databyte
        return ('ok',)

    def write(self, which):
        pid = self.sympid('Fs.write[%s].pid' % which)
        fd = simsym.SInt.any('Fs.write[%s].fd' % which)
        self.add_fdvar(fd)
        if not self.pid_map[pid].fd_map.contains(fd):
            return ('err', errno.EBADF)
        databyte = SDataByte.any('Fs.write[%s].data' % which)
        off = self.pid_map[pid].fd_map[fd].off
        self.pid_map[pid].fd_map[fd].off = off + 1
        return self.iwrite(self.pid_map[pid].fd_map[fd].inum, off, databyte)

    def pwrite(self, which):
        pid = self.sympid('Fs.pwrite[%s].pid' % which)
        fd = simsym.SInt.any('Fs.pwrite[%s].fd' % which)
        self.add_fdvar(fd)
        off = simsym.SInt.any('Fs.pwrite[%s].off' % which)
        self.add_offvar(off)
        if not self.pid_map[pid].fd_map.contains(fd):
            return ('err', errno.EBADF)
        databyte = SDataByte.any('Fs.pwrite[%s].databyte' % which)
        return self.iwrite(self.pid_map[pid].fd_map[fd].inum, off, databyte)

    def istat(self, inum):
        len = self.i_map[inum].data._len
        nlink = self.i_map[inum].nlink
        return ('ok', inum, len, nlink)

    def stat(self, which):
        pn = SPathname.any('Fs.stat[%s].pn' % which)
        _, dirmap, pnlast = self.nameiparent(pn)
        if not dirmap.contains(pnlast):
            return ('err', errno.ENOENT)
        return self.istat(dirmap[pnlast])

    def fstat(self, which):
        pid = self.sympid('Fs.fstat[%s].pid' % which)
        fd = simsym.SInt.any('Fs.fstat[%s].fd' % which)
        self.add_fdvar(fd)
        if not self.pid_map[pid].fd_map.contains(fd):
            return ('err', errno.EBADF)
        return self.istat(self.pid_map[pid].fd_map[fd].inum)

    def close(self, which):
        pid = self.sympid('Fs.close[%s].pid' % which)
        fd = simsym.SInt.any('Fs.close[%s].fd' % which)
        self.add_fdvar(fd)
        if not self.pid_map[pid].fd_map.contains(fd):
            return ('err', errno.EBADF)
        del self.pid_map[pid].fd_map[fd]
        return ('ok',)

model_class = Fs
model_functions = [
    Fs.open,
    Fs.pread,
    Fs.pwrite,
    Fs.read,
    Fs.write,
    Fs.unlink,
    Fs.link,
    Fs.rename,
    Fs.stat,
    Fs.fstat,
    Fs.close,
]