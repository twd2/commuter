import simsym
import model

class Counter(model.Struct):
    __slots__ = ["counter"]

    def __init__(self):
        # XXX This name matters since it connects the initial counter
        # value of different Counter objects.  Will this scale to more
        # complex state?
        self.counter = simsym.SInt.any('Counter.v')
        simsym.assume(self.counter >= 0)

    def sys_inc(self, which):
        self.counter = self.counter + 1

    def sys_dec(self, which):
        simsym.assume(self.counter > 0)
        self.counter = self.counter - 1

    def sys_iszero(self, which):
        return self.counter == 0

