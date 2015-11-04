class Pointer(object):

    def __init__(self, d):
        self.d = d
        self.indices = []

    @property
    def r(self):
        self.indices.append(1)
        return self

    @property
    def l(self):
        self.indices.append(0)
        return self

    @property
    def E(self):
        d = self.d
        for i in self.indices:
            d = d[i]
        return d

    # $ fun --m="&l"
    # (True, None)

    # $ fun --m="&ll"
    # ((True, None), None)


if __name__ == '__main__':
    d = (3, (1,(7,2)))
    p = Pointer(d)

    print p.r.r.l.E