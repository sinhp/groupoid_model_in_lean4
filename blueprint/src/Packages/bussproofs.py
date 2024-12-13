from plasTeX import VerbatimEnvironment

def ProcessOptions(options, document):
    document.config['images']['scales'].setdefault('prooftree', 1.5)

class prooftree(VerbatimEnvironment):
    pass
