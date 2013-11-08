from subprocess import call

files = [ 'bool'
        , 'basic_classes'
        , 'tuple'
        , 'maybe'
        , 'num'
        , 'list'
        , 'function'
        , 'either'
        , 'sorting'
        , 'set_helpers'
        , 'set'
        # , 'relation'
        , 'map'
        , 'pervasives'
        ]

lem_executable = '/home/dpm/Documents/Projects/Cambridge/bitbucket/lem/lem'
coq_executable = 'coqc'
rebuild_lem_sources = False

for file in files:
  lem_file = ''.join([file, '.lem'])
  coq_file = ''.join([file, '.v'])
  lem_command = [lem_executable, "-coq", lem_file]
  coq_command = [coq_executable, "-require", "coqharness", coq_file]
  lem_call = ' '.join(lem_command)
  coq_call = ' '.join(coq_command)
  if rebuild_lem_sources:
    print ('Compiling in Lem: ' + lem_call)
    call(lem_command)
  print ('Compiling in Coq: ' + coq_call)
  call(coq_command)