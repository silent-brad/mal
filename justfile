@help:
  echo "CljML Development"
  echo ""
  echo "Usage:"
  echo "  just <command>"
  echo ""
  echo "Commands:"
  echo "  fmt      Format OCaml + Clojure"
  echo "  build    Build CLJML Interpreter"
  echo "  run      Run CLJML Interpreter"

# Format OCaml + Clojure
@fmt:
  dune fmt
  cljstyle fix

# Build CLJML Interpreter
@build:
  dune build

# Run CLJML Interpreter
@run:
  dune exec cljml
