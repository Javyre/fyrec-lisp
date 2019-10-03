# Fyrec

The fyre compiler

## Building

First you need to [install roswell][1].

And then [qlot][2]:
```bash
ros install qlot
```

To build the project:
```
# to locally install the dependencies
ros exec qlot install

# to start a swank server with access to the local :fyrec system
ros exec qlot exec ros -S . -e '(ql:quickload :swank) (swank:create-server)'

# to run <cmd> <args>... with access to the local :fyrec system
ros exec qlot exec <cmd> <args>...
```

[1]: https://github.com/roswell/roswell/wiki/Installation
[2]: https://github.com/fukamachi/qlot
