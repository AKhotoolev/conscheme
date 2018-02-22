# conscheme

Conscheme is a fairly complete R5RS implementation in Go with some
important features missing: syntax-rules and full numeric tower.

## Background

Conscheme was a project to write a Scheme implementation in Google's
Go language. The project was led by Per Odlund and Göran Weinholt, who
were at the time master students at Chalmers University of Technology
in Gothenburg, Sweden. It was done as part of the Frontiers of
Programming Language Technology course in the spring of 2011.

## Current status

[![Build Status](https://travis-ci.org/weinholt/conscheme.svg?branch=master)](https://travis-ci.org/weinholt/conscheme)

The implementation has been updated to support newer golang versions.

## Installing

To run Conscheme you need a compiler for the Go language and a
workspace. Follow the instructions at http://golang.org/. Then build
the virtual machine:

```
$ go install github.com/weinholt/conscheme
```

This will install the github.com/weinholt/conscheme package and the
conscheme binary in the workspace. These contain a virtual machine and
a small image loader.

The boot image compiler/conscheme.image.pre-built should then be
copied to /usr/local/share/conscheme.image. Alternatively you may set
CONSCHEMEDIRS to a directory containing conscheme.image.

## Concurrency

Conscheme supports concurrency and provides simple message passing
inspired by Erlang. To enable Conscheme to run on multiple CPUs you
need to set the environment variable GOMAXPROCS to e.g. the number of
CPUs your system has. An example of how to use the concurrency support
is the parallel-map procedure provided in compiler/library.scm. The
send procedure currently doesn't guarantee relative message ordering.

## Development

Build the VM and ensure that you can start the pre-built image:

```
$ go build
$ ./conscheme -boot compiler/conscheme.image.pre-built
```

You should now see a Scheme REPL. To build your own image file, run
these commands:

```
$ cd compiler/
$ ../conscheme -boot ./conscheme.image.pre-built -c '(compile-bytecode "main.scm" "conscheme.image")'
```

The new image is now in conscheme.image and you no longer need to give
the -boot parameter. Conscheme searches for the image in a few
well-known locations, see conscheme.go for details.

Whenever you add new primitive procedures you need to regenerate
vm/primitives.go and recompile the conscheme package. This can be done
this way:

```
$ ../conscheme -c '(print-operations (current-output-port))' > ../vm/primitives.go
```

Conscheme can also be built by running the compiler in another Scheme.
During development we used GNU Guile 2.0. You might use this command
to build conscheme.image with Guile:

```
$ guile ./main.scm -c '(compile-bytecode "main.scm" "conscheme.image")'
```

The conscheme binary has profiling enabled. Run this to profile memory
allocation:

```
$ ./conscheme -memprofile conscheme.prof -script tests.scm
$ go tool pprof --alloc_objects ./conscheme conscheme.prof
```

Here's CPU profiling:

```
$ ./conscheme -cpuprofile conscheme.prof -script tests.scm
$ go tool pprof ./conscheme conscheme.prof
```

## Related software

https://github.com/SteelSeries/golisp
