#ifndef MBPUTILS__HPP__
#define MBPUTILS__HPP__

#include "ae/SMTUtils.hpp"
#include "ufo/Smt/EZ3.hh"

namespace ufo {
  Expr mixQE(Expr s, Expr eVar, ZSolver<EZ3>::Model &m, SMTUtils &u, int debug);

  enum laType {
    REALTYPE = 0,
    INTTYPE,
    MIXTYPE,
    NOTYPE
  };
}

#endif