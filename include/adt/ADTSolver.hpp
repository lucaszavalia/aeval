#ifndef ADTSOLVER__HPP__
#define ADTSOLVER__HPP__
#include <assert.h>
#include <string.h>
#include <fstream>

#include "ae/AeValSolver.hpp"
#include "ae/SMTUtils.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
namespace ufo
{
  class ADTSolver
  {
    private:

    Expr goal;
    ExprVector& assumptions;
    ExprVector& constructors;

    map<Expr, Expr> baseConstructors;
    map<Expr, Expr> indConstructors;

    ExprFactory &efac;
    SMTUtils u;

    // DS for lemma gen
    ExprVector baseconstrapps;
    ExprVector negativeLemmas;
    ExprVector positiveLemmas;

    //DS for disproof
    ExprSet compositeConstructors;
    int var_counter = 0;
    ExprSet types;
    ExprVector naturalNumbers;
    bool isNestedType = false;
    ExprVector blockedTypes; //mark for delete
    Expr templateFdecl; //mark for delete

    ExprVector rewriteHistory;
    vector<int> rewriteSequence;
    int maxDepth;
    int maxGrow;
    int mergingIts;
    int earlySplit;
    bool verbose;
    int sp = 2;
    int glob_ind = 0;
    int lev = 0;
    bool useZ3 = false;
    unsigned to;
    int disproofDepth = 0;
    ExprVector blockedAssms;
    int nestedLevel;

    public:

    ADTSolver(Expr _goal, ExprVector& _assumptions, ExprVector& _constructors,
      int _glob_ind = 0, int _lev = 0, int _maxDepth = 5, int _maxGrow = 3,
      int _mergingIts = 3, int _earlySplit = 1, bool _verbose = true,
      bool _useZ3 = true, unsigned _to = 1000, int _disproofDepth = 0, unsigned _l = 0) :
        goal(_goal), assumptions(_assumptions), constructors(_constructors),
        glob_ind(_glob_ind), lev(_lev), efac(_goal->getFactory()),
        u(_goal->getFactory(), _to), maxDepth(_maxDepth), maxGrow(_maxGrow),
        mergingIts(_mergingIts), earlySplit(_earlySplit), verbose(_verbose),
        useZ3(_useZ3), to (_to), disproofDepth(_disproofDepth), nestedLevel(_l)
    {
      // for convenience, rename assumptions (to have unique quantified variables)
      renameAssumptions();
    }

/*    void dumpToFile(Expr newGoal, ExprVector newAssms) {
       ofstream outputFile;
       outputFile.open("output.smt2", ofstream::out | ofstream::app);
       static bool didtypes = false;
       if (!didtypes) {
          serializeTypes(outputFile);
	  didtypes = true;
       }
       //for (auto & it : newAssms) {u.serialize_to_stream(it, outputFile);}
       u.serialize_to_stream(newGoal, outputFile);
       outputFile.close();
    }

    void serializeTypes(ostream & out = outs()) {
       //step 1, collect adt types and constructors
       map<Expr, ExprVector> newConstructors; //should have form <type, constructors>
       ExprVector typeVect;
       typeVect.resize(constructors.size());
       transform(constructors.begin(), constructors.end(), typeVect.begin(), [](Expr x){ return x->last(); });
       unique(typeVect.begin(), typeVect.end());
       for (auto & it : typeVect) {
          ExprVector tempCons;
	  tempCons.resize(constructors.size());
	  copy_if(constructors.begin(), constructors.end(), tempCons.begin(), [it](Expr x){return (x->last() == it);});
	  newConstructors.emplace(it, tempCons);
       }
       //step 2, iterate over newConstructors map and print info
       for (auto it : newConstructors) {
          out << "(declare-datatypes ";
	  out << "((" << it.first->arg(0); 
          out << " 0)) ";
	  out << "((";
	  for (auto is : it.second) {
	     out << "(" << is->arg(0);
	     if (is->arity() > 2) {out << " ";}
             for (int i = 1; i < is->arity() - 1; i++) {
                auto temp = is->arg(i);
		if (isOpX<AD_TY>(temp)) {
                   out <<  " (param" << i << " ";
		   out << temp->arg(0);
		   out << ")";
		}
		else {
                   out << "(param" << i << " ";
		   u.print(temp, out);
		   out << ")";
		}
	     }
	     out << ")";
	  }
	  out << "))";
	  out << ")\n";
       }
    }*/

    void renameAssumptions()
    {
      int c = 0;
      ExprSet allVars;
      filter(conjoin(assumptions, efac), bind::IsConst (), inserter(allVars, allVars.begin()));

      for (int i = 0; i < assumptions.size(); i++)
      {
        map<Expr, ExprVector> vars;
        getQVars(assumptions[i], vars);
        ExprMap replFls;
        for (auto & e : vars)
        {
          ExprMap repls;
          for (int j = 0; j < e.first->arity() - 1; j++)
          {
            Expr v = bind::fapp(e.first->arg(j));
            Expr newVar;
            while (true)
            {
              newVar = cloneVar(v, mkTerm<string> ("_qv_" + to_string(++c), efac));
              if (find(allVars.begin(), allVars.end(), newVar) == allVars.end()) break;
            }
            repls[v->left()->left()] = newVar->left()->left();
          }
          Expr newFla = replaceAll(e.first, replFls);
          replFls[e.first] = replaceAll(newFla, repls);
        }
        assumptions[i] = replaceAll(assumptions[i], replFls);
      }
    }

    bool simplifyGoal()
    {
      Expr goalQF = goal->last();
      if (containsOp<ITE>(goalQF)) // TODO: support IMPL/IFF
      {
        ExprVector disjs, vars;
        u.flatten(goalQF, disjs, false, vars, [](Expr a, ExprVector& b){return a;});
        goalQF = simplifyBool(disjoin(disjs, efac));
      }
      if (u.isEquiv(goalQF, mk<TRUE>(efac))) return true;

      ExprVector args;
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        if (contains(goal->last(), goal->arg(i))) args.push_back(goal->arg(i));
      }
      if (args.size() == 0) goal = goalQF;
      else
      {
        args.push_back(goalQF);
        goal = mknary<FORALL>(args);
      }
      rewriteHistory.push_back(goal);
      return false;
    }

    bool findAssmOccurs(Expr goal, Expr e, Expr eq)
    {
      for (auto a : assumptions)
      {
        if (a == eq) continue;
        if (contains(a, e)) return true;
      }
      return (contains(goal, e));
    }

    void eliminateEqualities(Expr& goal)
    {
      ExprMap allrepls;
      for (auto it = assumptions.begin(); it != assumptions.end();)
      {
        Expr &a = *it;
        if (isOpX<EQ>(a))
        {
          ExprMap repls;
          if (findAssmOccurs(goal, a->left(), a) > 0 && a->left()->arity() == 1
              && !contains (a->right(), a->left()))
            repls[a->left()] = a->right();
          else if (findAssmOccurs(goal, a->right(), a) > 0 && a->right()->arity() == 1
              && !contains (a->left(), a->right()))
            repls[a->right()] = a->left();

          if (repls.empty()) ++it;
          else
          {
            it = assumptions.erase(it);
            for (int i = 0; i < assumptions.size(); i++)
              assumptions[i] = replaceAll(assumptions[i], repls);
            goal = replaceAll(goal, repls);
          }
        }
        else ++it;
      }
    }

    bool mergeAssumptions(int bnd = -1)
    {
      // simplify them first
      int sz = assumptions.size();
      for (int i = 0; i < sz; i++) // TODO: add mores simplifications
      {
        Expr &a = assumptions[i];
        a = simplifyBool(a);
      }
      if (bnd == -1) bnd = mergingIts; // default val
      for (int i = 0; i < bnd; i++)
      {
        ExprSet newAssms;
        for (auto a : assumptions)
        {
          // todo: figure out why there could be NULLs
          if (a == NULL) continue;

          if (isOpX<ITE>(a))
          {
            newAssms.insert(a);
            continue; // GF: could be useful in principle
          }

          if (!isOpX<FORALL>(a) && simplifyAssm(a, newAssms))
          {
            return true;
          }
          if (isOpX<NEG>(a))
          {
            getConj(mkNeg(a->left()), newAssms);
          }
          else
          {
            newAssms.insert(a);
          }
        }
        assumptions.clear();
        for (auto & a : newAssms)
        {
          // some blocking heurisitcs here (TODO: try to block them in early stages, i.e., don't even compute)
          if (isOpX<EQ>(a) && isOpX<AND>(a->left()) /*&& isOpX<AND>(a->right())*/) continue;

          if (find (blockedAssms.begin(), blockedAssms.end(), a) == blockedAssms.end())
            unique_push_back(a, assumptions);
        }
      }
      return false;
    }

    void splitAssumptions()
    {
      ExprSet newAssms;
      for (auto & a : assumptions)
      {
        if (a != NULL) getConj(a, newAssms);
      }
      assumptions.clear();
      for (auto & a : newAssms) assumptions.push_back(a);
    }

    bool simplifyAssm(Expr assm, ExprSet& newAssms)
    {
      for (auto a : assumptions)
      {
        if (a == assm || a == NULL) continue;
        if (isOpX<FORALL>(assm) && !isOpX<FORALL>(a)) continue;

        ExprVector result;
        if (useAssumption(assm, a, result, true)) {
          for (auto & it : result) {
            if (it == NULL) continue;

            Expr tmp = it;
            if (!u.isTrue(tmp))
              {
              if (u.isFalse(tmp))
              {
                if (verbose) outs () << string(sp, ' ')
                  << "inconsistent assumptions: " << *assm << " and " << *a << "\n";
                return true;
              }

              tmp = simplifyArithm(tmp);
              ExprSet tmps;
              getConj(simplifyBool(tmp), tmps);
              getConj(simplifyBool(simplifyArr(tmp)), tmps); // duplicate for the case of arrays
              for (auto & t : tmps)
              {
                if (find(assumptions.begin(), assumptions.end(), t) == assumptions.end())
                {
                  newAssms.insert(t);
                }
              }
            }
          }
        }
      }
      return false;
    }

    // main method to do rewriting
    // TODO: separate the logic for fwd, otherwise the code gets messy
    bool useAssumption(Expr subgoal, Expr assm, ExprVector& result, bool fwd = false)
    {
      if (isOpX<FORALL>(assm))
      {
        ExprMap matching;
        ExprVector args;
        for (int i = 0; i < assm->arity() - 1; i++) args.push_back(bind::fapp(assm->arg(i)));

        Expr assmQF = assm->last();
        Expr repl = assmQF;

        bool isImpl = false;
        if (isOpX<IMPL>(assmQF))
        {
          if (fwd) assmQF = assmQF->left();
          else assmQF = assmQF->right();
          isImpl = true;
        }

        if (isOpX<ITE>(assmQF))
        {
          int res = -1;
          if (fwd)
          {
            if (findMatching (assmQF->left(), subgoal, args, matching))
            {
              res = 1;
            }
            else
            {
              matching.clear();
              if (findMatching (mkNeg(assmQF->left()), subgoal, args, matching))
              {
                res = 2;
              }
            }
            if (res > 0)
            {
              repl = replaceAll(assmQF->arg(res), matching);

              // sanity removal
              for (auto it = args.begin(); it != args.end();)
              {
                if (contains (repl, *it)) ++it;
                else it = args.erase(it);
              }

              if (!args.empty())
              {
                repl = createQuantifiedFormulaRestr(repl, args);
              }

              result.push_back(repl);
              return true;
            }
          }
          else
          {
            // !fwd

            if (findMatching (assmQF->right(), subgoal, args, matching))
            {
              res = 1;
            }
            else
            {
              matching.clear();
              if (findMatching (assmQF->last(), subgoal, args, matching))
              {
                res = 2;
              }
            }
            if (res > 0)
            {
              if (res == 1) repl = assmQF->left();
              else repl = mkNeg(assmQF->left());
              repl = replaceAll(repl, matching);

              ExprSet vars;
              filter(assmQF->left(), bind::IsConst (), inserter(vars, vars.begin()));

              for (auto it = args.begin(); it != args.end();)
              {
                if (find(vars.begin(), vars.end(), *it) != vars.end())
                {
                  it = args.erase(it);
                }
                else
                {
                  ++it;
                }
              }
              if (!args.empty()) repl = createQuantifiedFormulaRestr(repl, args, false);

              result.push_back(repl);
              return true;
            }
          }
        }

        std::set<ExprMap> matchingSet;
        // we first search for a matching of the entire assumption (usually some inequality)
        if (findMatchingSubexpr (assmQF, subgoal, args, matchingSet))
        {
          for (auto matching : matchingSet) {
            Expr auxRepl = repl;
            auxRepl = replaceAll(auxRepl, matching);
            Expr replaced;
            if (isImpl)
            {
              if (fwd) // used in simplifyAssm
              {
                if (!isOpX<FORALL>(subgoal) && u.implies(subgoal, auxRepl->left()))
                {
                  ExprSet vars;
                  filter (assmQF, bind::IsConst (), inserter(vars, vars.begin()));
                  for (auto it = args.begin(); it != args.end();)
                  {
                    bool found = false;
                    if (find(vars.begin(), vars.end(), *it) != vars.end())
                    {
                      found = true;
                      it = args.erase(it);
                    }
                    if (!found)
                    {
                      ++it;
                    }
                  }

                  // sanity removal
                  for (auto it = args.begin(); it != args.end();)
                  {
                    if (contains (auxRepl->right(), *it)) ++it;
                    else it = args.erase(it);
                  }

                  if (args.empty())
                  {
                    replaced = auxRepl->right();
                  }
                  else
                  {
                    replaced = createQuantifiedFormulaRestr(auxRepl->right(), args);
                  }
                }
              }
              else
              {
                ExprSet vars;
                filter(assmQF, bind::IsConst (), inserter(vars, vars.begin()));
                replaced = replaceAll(subgoal, auxRepl->right(), auxRepl->left());

                for (auto it = args.begin(); it != args.end();)
                {
                  if (find(vars.begin(), vars.end(), *it) != vars.end())
                  {
                    it = args.erase(it);
                  }
                  else
                  {
                    ++it;
                  }
                }
                if (!args.empty())
                  replaced = createQuantifiedFormulaRestr(replaced, args, false);
              }
            }
            else
            {
              replaced = replaceAll(subgoal, auxRepl, mk<TRUE>(efac));
            }

            if (subgoal != replaced)
            {
              result.push_back(replaced);
              return true;
            }
          }
        }

        if (isImpl) return false;

        if (isOpX<EQ>(assmQF))
        {
          matchingSet.clear();
          // if the assumption is equality, the we search for a matching of its LHS
          // (we can try matching the RHS as well, but it will likely give us infinite loops)
          if (findMatchingSubexpr (assmQF->left(), subgoal, args, matchingSet))
          {
            for (auto matching : matchingSet) {
              Expr auxRepl = repl;
              auxRepl = replaceAll(auxRepl, matching);
              result.push_back(replaceAll(subgoal, auxRepl->left(), auxRepl->right()));
            }
            return true;
          }
          // try vice versa (dangerous since it will introduce repeated rewriting)
          // matchingSet.clear();
          // if (!fwd && findMatchingSubexpr (assmQF->right(), subgoal, args, matchingSet))
          // {
          //   for (auto matching : matchingSet) {
          //     Expr auxRepl = repl;
          //     auxRepl = replaceAll(auxRepl, matching);
          //     result.push_back(replaceAll(subgoal, auxRepl->right(), auxRepl->left()));
          //   }
          //   return true;
          // }
        }

        if (isOp<ComparissonOp>(assmQF) && isOp<ComparissonOp>(subgoal))
        {
          Expr assmQFtmp = assmQF;
          Expr subgoalTmp = subgoal;
          assmQF = normalizeArithm(assmQF);
          subgoal = normalizeArithm(subgoal);

          if (findMatching (assmQF->left(), subgoal->left(), args, matching))
          {
            repl = replaceAll(assmQF, matching);
            if (fwd && !u.isSat(repl, subgoal))
            {
              result.push_back(mk<FALSE>(efac));
              return true;
            }
            if (fwd)
            {
              if (((isOpX<LEQ>(repl) && isOpX<GEQ>(subgoal)) || (isOpX<GEQ>(repl) && isOpX<LEQ>(subgoal))) &&
                  (repl->left() == subgoal->left()) && (repl->right() == subgoal->right()))
                {
                  result.push_back(mk<EQ>(repl->left(), subgoal->right()));
                  return true;
                }
            }
            if (!fwd && u.implies(repl, subgoal))
            {
              result.push_back(mk<TRUE>(efac));
              return true;
            }
          }
          matching.clear();
          assmQF = assmQFtmp;
          subgoal = subgoalTmp;
        }

        if (isOpX<ITE>(subgoal))
        {
          matchingSet.clear();
          if (findMatchingSubexpr (assmQF, subgoal->left(), args, matchingSet))
          {
            for (auto matching : matchingSet) {
              Expr auxRepl = repl;
              for (auto & a : matching) auxRepl = replaceAll(auxRepl, a.first, a.second);
              if (u.implies(auxRepl, subgoal->left())) result.push_back(subgoal->right());
              else if (u.implies(auxRepl, mkNeg(subgoal->left()))) result.push_back(subgoal->last());
            }
            return (result.size() > 0);
          }
        }

        // try finding inconsistencies
        if (fwd && !containsOp<FORALL>(assmQF))
        {
          std::set<ExprMap> matchingSet1;
          ExprVector args1;
          filter(subgoal, bind::IsConst (), inserter(args1, args1.begin()));
          if (findMatchingSubexpr (subgoal, assmQF, args1, matchingSet1))
          {
            for (auto matching1 : matchingSet1) {
              Expr auxRepl = assmQF;
              for (auto & m : matching1){
                auto it = find(args.begin(), args.end(), m.second);
                if (it != args.end())
                {
                  auxRepl = replaceAll(auxRepl, m.second, m.first);
                  args.erase(it);
                }
                else
                {
                  if (m.second != m.first) break;
                }
              }
              if (args.empty())
              {
                if (!u.isSat(subgoal, auxRepl)) result.push_back(mk<FALSE>(efac));
                else result.push_back(auxRepl);
                return true;
              }
            }
          }
        }
      }
      else
      {
        // for a quantifier-free assumption (e.g., inductive hypotheses),
        // we create an SMT query and check with Z3
        // TODO: we can do so for ALL constistent quantifier-free assumptions at once

        if (isOpX<EQ>(assm)) // simple (SMT-free) checks first
        {
          Expr res = replaceAll(subgoal, assm->left(), assm->right());
          if (res != subgoal)
          {
            result.push_back(res);
            return true;
          }
        }

        if (!fwd && u.implies(assm, subgoal))
        {
          result.push_back(mk<TRUE>(efac));
          return true;
        }
        if (fwd && !u.isSat(assm, subgoal)) {
          result.push_back(mk<FALSE>(efac));
          return true;
        }

        if (!fwd && isOp<ComparissonOp>(subgoal) && isOp<ComparissonOp>(assm) &&
            isNumeric(subgoal->left()) && isNumeric(assm->left()))
        {
          Expr tryAbd = abduce(subgoal, assm);
          if (tryAbd != NULL && tryAbd != subgoal)
          {
            result.push_back(tryAbd);
            return true;
          }
        }

        // TODO: proper matching
        if (isOpX<IMPL>(subgoal))
        {
          if (u.implies(subgoal->left(), assm))
          {
            result.push_back(subgoal->right());
            return true;
          }
        }
        if (isOpX<ITE>(subgoal))
        {
          if (u.implies(assm, subgoal->left()))
          {
            result.push_back(subgoal->right());
            return true;
          }
          if (u.implies(assm, mk<NEG>(subgoal->left())))
          {
            result.push_back(subgoal->last());
            return true;
          }
        }

        if (isOpX<OR>(assm) && fwd)
        {
          ExprSet dsjs;
          getDisj(assm, dsjs);
          bool rem = false;
          for (auto it = dsjs.begin(); it != dsjs.end();)
          {
            if (!u.isSat(*it, subgoal))
            {
              rem = true;
              it = dsjs.erase(it);
            }
            else ++it;
          }
          if (rem)
          {
            Expr res = disjoin(dsjs, efac);
            result.push_back(res);
            return true;
          }
        }
        if (isOp<ComparissonOp>(assm))
        {
          Expr res = replaceAll(subgoal, assm, mk<TRUE>(efac));
          res = replaceAll(res, mkNeg(assm), mk<FALSE>(efac));
          Expr tmp = reBuildCmpSym(assm, assm->left(), assm->right());
          assert((bool)u.isEquiv(assm, tmp));
          res = replaceAll(res, tmp, mk<TRUE>(efac));
          res = replaceAll(res, mkNeg(tmp), mk<FALSE>(efac));
          if (res != subgoal)
          {
            result.push_back(simplifyBool(res));
            return true;
          }
        }

        ExprSet stores;
        ExprSet selects;
        getStores(subgoal, stores);
        getSelects(subgoal, selects);

        if (stores.size() > 0)
        {
          if (isOpX<NEQ>(assm) && contains(subgoal, assm->left()) && contains(subgoal, assm->right()))
          {
            for (auto & a : stores)
            {
              if (isOpX<STORE>(a->left()) &&
                  ((a->right() == assm->right() && a->left()->right() == assm->left()) ||
                   (a->right() == assm->left() && a->left()->right() == assm->right())))
              {
                ExprMap substs;
                substs[assm->right()] = assm->left();
                substs[assm->left()] = assm->right();
                Expr tmp = replaceAll(a, substs, false);

                if (u.implies(assm, mk<EQ>(tmp, a)))
                {
                  result.push_back(replaceAll(subgoal, a, tmp));   // very specific heuristic; works for multisets
                  return true;
                }

                if (a->last() != a->left()->last())
                {
                  substs[a->last()] = a->left()->last();
                  substs[a->left()->last()] = a->last();
                }
                result.push_back(replaceAll(subgoal, a, replaceAll(a, substs, false)));
                return true;
              }
            }
            for (auto & a : selects)
            {
              if (isOpX<STORE>(a->left()) && !isOpX<STORE>(a->left()->left()) &&
                  ((a->right() == assm->right() && a->left()->right() == assm->left()) ||
                   (a->right() == assm->left() && a->left()->right() == assm->right())))
              {
                result.push_back(replaceAll(subgoal, a, mk<SELECT>(a->left()->left(), a->right())));
                return true;
              }
            }
          }

          if (isOpX<SELECT>(assm))
          {

            for (auto & a : stores)
            {
              if (assm->left() == a->left() &&
                  assm->right() == a->right() &&
                  isOpX<TRUE>(a->last()))
              {
                result.push_back(replaceAll(subgoal, a, a->left()));
                return true;
              }
            }
          }

          if (isOpX<NEG>(assm) && isOpX<SELECT>(assm->left()))
          {
            for (auto & a : stores)
            {
              if (assm->left()->left() == a->left() &&
                  assm->left()->right() == a->right() &&
                  isOpX<FALSE>(a->last()))
              {
                result.push_back(replaceAll(subgoal, a, a->left()));
                return true;
              }
            }
          }
        }
      }
      return false;
    }

    bool handleExists(Expr subgoal)
    {
      if (verbose) outs () << string(sp, ' ')  << "existential quantifies are currently not supported\n";
      return false;
      // to be done
    }

    // this recursive method performs a naive search for a strategy
    bool rewriteAssumptions(Expr subgoal)
    {
      if (u.isEquiv(subgoal, mk<TRUE>(efac)))
      {
        if (verbose) outs () << string(sp, ' ') << "rewriting done\n";
        return true;
      }

      // check recursion depth
      if (rewriteSequence.size() >= maxDepth)
      {
        if (verbose) outs() << string(sp, ' ') << "Maximum recursion depth reached\n";
        return false;
      }

      // check consecutive applications of the same assumption
      if (rewriteSequence.size() > maxGrow)
      {
        bool incr = true;
        for (int i = 1; i < maxGrow + 1; i++)
        {
          if (treeSize(rewriteHistory[rewriteHistory.size() - i]) < treeSize(rewriteHistory[rewriteHistory.size() - i - 1]))
          {
            incr = false;
            break;
          }
        }

        if (incr)
        {
          if (verbose) outs() << string(sp, ' ') << "sequence of rewrites only grows\n";
          return false;
        }
      }

      auto assumptionsTmp = assumptions;
      bool toRem = false;
      if (isOpX<IMPL>(subgoal))
      {
        uniquePushConj(subgoal->left(), assumptions);
        if (assumptions.size() != assumptionsTmp.size())
        {
          eliminateEqualities(subgoal);
          toRem = true;
          if (mergeAssumptions())
          {
            assumptions = assumptionsTmp;
            if (verbose) outs() << string(sp, ' ') << "proven (merge assms after impl)\n";
            return true;
          }
          printAssumptions();
        }
        subgoal = subgoal->right();
        if (verbose) outs() << string(sp, ' ') << "current subgoal: " << *subgoal << "\n";
      }

      if (isOpX<EXISTS>(subgoal))
      {
        return handleExists(subgoal);
      }

      subgoal = simplifyExists(subgoal);
      subgoal = simplifyArr(subgoal);
      subgoal = simplifyArithm(subgoal);
      subgoal = simplifyBool(subgoal);

      ExprSet subgoals;
      if (isOpX<ITE>(subgoal))
      {
        subgoals.insert(mk<IMPL>(subgoal->left(), subgoal->right()));
        subgoals.insert(mk<IMPL>(mkNeg(subgoal->left()), subgoal->last()));
      }
      else
      {
        getConj(subgoal, subgoals);
      }

      if (subgoals.size() > 1)
      {
        while (subgoals.size() > 0)
        {
          int subgoalsSize = subgoals.size();
          int part = 1;
          for (auto it = subgoals.begin(); it != subgoals.end();)
          {
            Expr s = *it;
            if (verbose)
            {
              outs () << string(sp, ' ') << "proceed with (part " << part << "/" << subgoalsSize << "): " << *s << "\n";
              part++;
            }

            tribool tmpres = simpleSMTcheck(s);
            if (tmpres)
            {
              if (verbose) outs() << string(sp, ' ') << "{\n" << string(sp+2, ' ') <<
                "  proven trivially (with Z3)\n" << string(sp, ' ') << "}\n";
            }
            else
            {
              auto rewriteHistoryTmp = rewriteHistory;
              auto rewriteSequenceTmp = rewriteSequence;
              auto assumptionsTmp = assumptions;

              if (verbose) outs() << string(sp, ' ') << "{\n";
              sp += 2;
              tmpres = rewriteAssumptions(s);   // recursive call
              sp -= 2;
              if (verbose) outs() << string(sp, ' ') << "}\n";

              rewriteHistory = rewriteHistoryTmp;
              rewriteSequence = rewriteSequenceTmp;
              assumptions = assumptionsTmp;
            }
            if (tmpres)
            {
              if (verbose) outs () << string(sp, ' ') << "adding " << *s << " to assumptions\n";
              assumptions.push_back(s);
              it = subgoals.erase(it);
            }
            else
            {
              ++it;
            }
          }
          if (subgoals.size() == subgoalsSize)
          {
            if (verbose) outs() << string(sp, ' ') << "cannot prove " << subgoalsSize << " of the subgoals\n";
            return false;
          }
          else if (verbose && subgoals.size() > 0) outs () << string(sp, ' ') << "will try subgoals again\n";
        }
        if (verbose) outs () << string(sp, ' ')  << "all subgoals are proven\n";
        return true;
      }

      // here, assume subgoals.size() == 1
      // thus, subgoal == *subgoals.begin()

      // quick syntactic check first:
      for (int i = 0; i < assumptions.size(); i++)
      {
        if (assumptions[i] == subgoal)
        {
          if (toRem) assumptions = assumptionsTmp;
          if (verbose) outs () << string(sp, ' ') << "rewriting [" << i << "] done\n";
          return true;
        }
      }

      map<int, ExprVector> allAttempts;

      for (int i = 0; i < assumptions.size(); i++)
      {
        Expr a = assumptions[i];
        ExprVector result;
        if (useAssumption(subgoal, a, result)) {
//          if (verbose) outs () << string(sp, ' ') << "found " << result.size() << " substitution(s) for assumption " << i << "\n";
          for (auto & it : result) {
            if (u.isTrue(it))
            {
              if (verbose) outs () << string(sp, ' ') << "applied [" << i << "]\n";
              return true;
            }
          }
          for (auto & it : result)
            if (find (rewriteHistory.begin(), rewriteHistory.end(), it) == rewriteHistory.end())
              allAttempts[i].push_back(it);
        }
      }
      {
      // vector<int> orderedAttempts1;
      // vector<int> orderedAttempts2;

      // identifying an order for rewrites
      // for (auto & a : allAttempts)
      // {
      //   bool placed = false;

      //   bool sw;
      //   if (earlySplit == 1) sw = treeSize(subgoal) >= treeSize(a.second);
      //   else sw = true;

      //   if (sw)
      //   {
      //     for (int i = 0; i < orderedAttempts1.size(); i++)
      //     {
      //       if (treeSize(allAttempts[orderedAttempts1[i]]) > treeSize(a.second))
      //       {
      //         orderedAttempts1.insert(orderedAttempts1.begin() + i, a.first);
      //         placed = true;
      //         break;
      //       }
      //     }
      //     if (!placed) orderedAttempts1.push_back(a.first);
      //   }
      //   else
      //   {
      //     for (int i = 0; i < orderedAttempts2.size(); i++)
      //     {
      //       if (treeSize(allAttempts[orderedAttempts2[i]]) > treeSize(a.second))
      //       {
      //         orderedAttempts2.insert(orderedAttempts2.begin() + i, a.first);
      //         placed = true;
      //         break;
      //       }
      //     }
      //     if (!placed) orderedAttempts2.push_back(a.first);
      //   }
      // }
      }

      if (tryRewriting(allAttempts, subgoal))
      {
        if (toRem) assumptions = assumptionsTmp;
        return true;
      }

      if (splitDisjAssumptions(subgoal)) return true;

      bool res = false;

      if (isOpX<OR>(subgoal)) res = splitByGoal(subgoal);
//      if (!res) res = proveByContradiction(subgoal);
//      if (!res) res = similarityHeuristic(subgoal);
      if (toRem) assumptions = assumptionsTmp;
      if (res) return true;

      if (lemmaGen(subgoal)) return true;

      // backtrack:
      if (verbose) outs () << string(sp, ' ') << "backtrack to: " << *subgoal << "\n";
      return res;
    }

    bool lemmaGen(Expr subgoal)
    {
      if (lev < 1 /* max meta-induction level, hardcoded for now */)
      {
        map<Expr, int> occs;
        getCommonSubterms(subgoal, occs);   // get common subterms in `exp` to further replace by fresh symbols
        auto it = occs.begin();
        for (int i = 0; i < occs.size() + 1; i++)
        {
          Expr expGen = subgoal;
          if (it != occs.end()) // try generalizing based on the current subterm from occs
          {
            expGen = generalizeGoal(subgoal, it->first, it->second);
            ++it;
            if (expGen == NULL) continue;
          }
          else
          {
            // if nothing worked, try to prove it as is (exactly once, but if not very large)
            if (getMonotDegree(expGen) > 2 || countFuns(expGen) > 3) //  hand-selected heuristics
              continue;
          }

          ExprVector vars;
          filter (expGen, IsConst (), inserter(vars, vars.begin()));
          for (auto it = vars.begin(); it != vars.end();)
            if (find(baseconstrapps.begin(), baseconstrapps.end(), *it) == baseconstrapps.end()) ++it;
              else it = vars.erase(it);

          bool toCont = false;
          for (auto & l : negativeLemmas)
          {
            ExprMap matching;
            if (findMatching(expGen, l, vars, matching))
            {
              toCont = true;
              break;
            }
          }
          if (toCont) continue;

          for (auto & l : positiveLemmas)
          {
            ExprMap matching;
            if (findMatching(expGen, l, vars, matching))
            {
              toCont = true;
              break;
            }
          }

          if (!toCont)
          {
            auto assumptionsNst = assumptions;
            for (auto it = assumptionsNst.begin(); it != assumptionsNst.end();)
              if (hasOnlyVars(*it, baseconstrapps)) ++it;
                else it = assumptionsNst.erase(it);
	    
	    //try to disprove lemma
	    int tempDepth = disproofDepth;
	    disproofDepth = 2;
            auto newExp = mkQFla(expGen, vars);
	    if (bool(disproof(newExp))) {
                disproofDepth = tempDepth;
		outs() << string(sp, ' ') << "Unknown\n";
		continue;
	    }
	    disproofDepth = tempDepth;

	    //auto newExp = mkQFla(expGen, vars);
            ADTSolver sol (newExp, assumptionsNst, constructors, glob_ind, lev + 1,
                           maxDepth, maxGrow, mergingIts, earlySplit, false, useZ3, to, disproofDepth);
            toCont = bool(sol.solve());
	  }
          if (toCont)
          {
            if (verbose) outs () << string(sp, ' ')  << "proven by induction: " << *expGen << "\n";
            positiveLemmas.push_back(expGen);
            return true;
          }
          else
          {
            if (verbose) outs () << string(sp, ' ')  << "nested induction failed\n";
            negativeLemmas.push_back(expGen);
          }
	  /*auto newExp = mkQFla(expGen, vars);
	  if (bool(disproof(newExp))) {
             outs() << "Unknown\n";
	     exit(1);
	  }*/
        }
      }
      return false;
    }

    // try rewriting in a particular order
    bool tryRewriting(map<int, ExprVector>& allAttempts, Expr subgoal)
    {
      for (auto & a : allAttempts) {
        int i = a.first;
        for (auto & exp : a.second) {
          if (verbose) outs() << string(sp, ' ') << "rewritten [" << i << "]: " << *exp << "\n";

          // save history
          rewriteHistory.push_back(exp);
          rewriteSequence.push_back(i);

          if (rewriteAssumptions(exp))
          {
            if (verbose) if (exp) outs () << string(sp, ' ')  << "rewriting done\n";
            return true;
          }
          else
          {
            // failed attempt, remove history
            rewriteHistory.pop_back();
            rewriteSequence.pop_back();
          }
        }
      }
      return false;
    }

    // a particular heuristic, to be extended
    Expr generalizeGoal(Expr e, Expr subterm, int occs /* how often `subterm` occurs in `e` */)
    {
      if (occs < 1) return NULL;
      if (subterm->arity() == 0 && !isOpX<MPZ>(subterm))
        return NULL;                                      // it should not be a (non-integer) constant
      if (isOpX<FAPP>(subterm) &&
          subterm->left()->arity() == 2) return NULL;     // it should not be a variable
      Expr expGen = e;
      Expr s = bind::mkConst(mkTerm<string> ("_w_" + to_string(glob_ind), efac), typeOf(subterm));
      glob_ind++;                                         // create a fresh symmbol
      expGen = replaceAll(expGen, subterm, s);
      if (isOpX<MPZ>(subterm))                            // replace negative consts
        expGen = replaceAll(expGen, mkMPZ(-lexical_cast<cpp_int>(subterm), efac),
                                    mk<UN_MINUS>(s));;
      if (!emptyIntersect(expGen, subterm)) return NULL;  // there should not be any leftovers after replacement
      int cnt = countFuns(expGen);                        // check the result
      if (cnt == 0 || cnt > 3) return NULL;
      if (getMonotDegree(expGen) > 2) return NULL;        // if it is still "too complex", scratch it
      return expGen;
    }

    //test this function with more rigor before rerunning experiments
    bool disproofFilter2(Expr & exp) {
       //outs() << "expression head is: " << exp->arg(0) << '\n';
       if (!isOpX<FAPP>(exp)) {
	  ExprSet fdecls;
	  //outs() << "PING\n";
          filter(exp, [](Expr & x){return (isOpX<FDECL>(x) && x->arity() > 2);}, inserter(fdecls, fdecls.begin()));
	  //collect all non-variable fdecls in exp
	  //outs() << "fdecls are: ";
	  //for (auto & it : fdecls) {outs() << it << ' ';}
	  //outs() << '\n';
	  //if there are no fdecls, send to z3 (might be arithmetic term)
	  if (fdecls.empty()) {return true;}
	  //test if each fdecl is in constructors 
	  bool isSubset = true;
	  for (auto & it : fdecls) {
             if (find(constructors.begin(), constructors.end(), it) == constructors.end()) {isSubset = false;}
	  }
	  return isSubset;
       }
       outs() << string(sp, ' ') << "filter failed\n";
       return false;
    }

    tribool disproof(Expr exp) {
       outs() << string(sp, ' ') << "Attempting to disprove: " << exp << '\n';
       outs() << string(sp, ' ') << "Disproof depth is set to: " << disproofDepth << '\n';
       outs() << string(sp, ' ') << "{\n";
       ExprVector vars;
       Expr newExpr;
       //compute types set and natural number vector, used for handling nested adts
       for (auto & it : constructors) {
          types.insert(it->last());
       }
       naturalNumbers = getNaturalNumbers();
       //remove quantifier
       if (isOpX<FORALL>(exp) || isOpX<EXISTS>(exp)) {newExpr = exp->last();}
       else {newExpr = exp;}
       //collect finalTerms
       ExprSet finalTerms = generateTerms(newExpr, disproofDepth);
       //get template for nested ADT handler
       Expr candidate_fdecl;
       if (!finalTerms.empty()) {
          auto tempIter = *(finalTerms.begin()++);
	  candidate_fdecl = templateFdecl;
	  //outs() << "Candidate fdecl is " << candidate_fdecl << '\n';
       }
       outs() << string(sp + 2, ' ') << "generated " << finalTerms.size() << " terms {\n";
       for (auto & it : finalTerms){outs() << string(sp + 4, ' ') << it << "\n";}
       outs() << string(sp + 2, ' ') << "}\n";
       outs() << string(sp + 2, ' ') << "unfolding terms\n";
       int counter = 0;
       int breaker = 0;
       for (auto it = finalTerms.begin(); it != finalTerms.end(); it++) {
          Expr temp = *it;
          Expr old = temp;
          while (true) { // this portion will need to be a recursive function (for completeness, not as important)
             ExprVector results;
             for (auto is = assumptions.begin(); is != assumptions.end(); is++) {
                //locate specific function definitions
                //when reading file, extract definitions
                //pattern match for two assumptions, one will have base cons the other will be ind
                //
                useAssumption(temp, *is, results);
                if (!results.empty()) {
                   temp = results[0];
                }
             }
	     //make a filter to keep nonsense from going to z3 (more important)
             if (old == temp) {break;}
             else {old = temp;}
             //if (isOpX<TRUE>(temp)) break;
          }
          outs() << string(sp + 2, ' ') << "unfolded term: " << temp << '\n';
	  if (isOpX<TRUE>(temp)){continue;}
	  Expr trans;
	  auto syn_res = syntaxTransformation1(temp, trans);
	  bool isSame = false;
	  bool resNested = false;
	  if (syn_res) {
             if (temp == trans) {isSame = true;}
             temp = trans;
	  }
	  else {
             outs() << string(sp + 2, ' ') << "Syntactic check failed for " << temp << '\n';
	     return true;
	  }
	  if (isNestedType) {
             Expr newTemp = syntaxTransformation2(temp);
	     if (newTemp == NULL) {
                outs() << string(sp + 2, ' ') << "Syntactic check failed for " << temp << '\n';
		return true;
	     }
	     temp = newTemp;
	     resNested = true;
	  }
	  //Expr throwAway = nestedADTHandler(temp, candidate_fdecl);
	  //outs() << "Unfolded nest ADT is: " << throwAway << '\n';
	  //temp = throwAway;
	  //
	  //dumpToFile(constructors, assumptions, temp, true);
          //outs() << "    counter: " << counter << '\n';
          counter++;
	  outs() << string(sp + 2, ' ') << "transformed term: " << temp << '\n';
	  if (!disproofFilter2(temp)) {
	     outs() << string(sp + 2, ' ') << "unfolding failed at term " << temp << '\n';
             continue;
	  }
          //temp = mk<IMPL>(temp, mk<TRUE>(efac));          
	  auto ttt = u.isSat(temp);
	  Expr model;
	  if ((ttt == true && isSame != true) || (ttt != true && isSame == true) || (ttt != true && resNested == true))
	  {
	     outs() << string(sp + 2, ' ') << "Last term is " << temp << '\n';
             model = u.getModel();
	     //if (isOpX<TRUE>(model)) {continue;}
	     // TODO: report disproof
             outs() << string(sp + 2, ' ') << "Disproven with Z3.\n";
	     outs() << string(sp + 2, ' ') << "Counterexample: " << model << '\n';
             outs() << string(sp, ' ') << "}\n";
             return true;
          }
          if (counter == 20 || counter == finalTerms.size() - 1) {
            outs() << string(sp + 2, ' ') << "Tested maximum number of terms\n";
            outs() << string(sp, ' ') << "}\n";
            return indeterminate;
          };
       }
       outs() << string(sp + 2, ' ') << "Disproof failed.\n";
       outs() << string(sp, ' ') << "}\n";
       //experiment here with useAssumption, run on an infinite loop that replaces each rev2 instance one at a time
       return indeterminate;
    }

    ExprSet generateTerms(Expr exp, int length) {
       ExprSet startSet;
       ExprSet results;
       startSet.insert(exp);
       //collect variables and remove constants
       ExprVector vars;
       filter(exp, bind::IsConst(), inserter(vars, vars.begin()));
       Expr base =  mk<FAPP>(*find_if(constructors.begin(), constructors.end(), [](Expr x){return x->arity() == 2;}));
       for (auto it = vars.begin(); it != vars.end(); ) {
         if (*it == base) {vars.erase(it);}
         else it++;
       }
       //call unwrapped function
       generateTermsUnwrapped(exp, startSet, vars, length, results);
       return results;
    }

    void generateTermsUnwrapped(Expr exp, ExprSet start, ExprVector vars, int length, ExprSet & result) {
       if (vars.empty()) {
         result = start;
         return;
       }
       ExprSet newSet;
       Expr curVar = vars.back();
       vars.pop_back();

       Expr old = mk<TRUE>(efac);
       ExprSet newTerms = processTerms(exp, length);
       auto curVarType = curVar->last()->last();
       for (auto it = start.begin(); it != start.end(); it++) {
          for (auto is = newTerms.begin(); is != newTerms.end(); is++) {
             if (curVarType == getADTType(*is)) {		
		auto new_term = *is;
		bool res = testIsomorphism(old, new_term);
		bool normal = false;
		if (!normal) {
                   if (!res) {
		      Expr temp = replaceAll(*it, curVar, *is);
                      newSet.insert(temp);
		   }
		}
		else {
                   Expr temp = replaceAll(*it, curVar, *is);
		   newSet.insert(temp);
		}
/*
		outs() << string(sp+4, ' ') << "Current term: " << temp << '\n';
		outs() << string(sp+4, ' ') << "Substitution: " << *is << '\n';
		outs() << string(sp+4, ' ') << "Old data is : " << old << '\n';
		outs() << string(sp+4, ' ') << "Result is   : " << res << '\n';*/
             }
	     old = * is;
          }
       }
       generateTermsUnwrapped(exp, newSet, vars, length, result);
    }

    ExprSet processTerms(Expr exp, int length) {
       ExprSet result;
       ExprSet startSet;
       ExprSet generatedTerms;
       for (auto & it : constructors) {
          if (it->arity() > 2) {
             auto base = mk<FAPP>(*find_if(constructors.begin(), constructors.end(), [it](Expr x){return (x->arity() == 2 && x->last() == it->last());}));
             ExprSet tempSet;
	     ExprSet finalSet;
             tempSet.insert(base);
	     ExprSet vars;
             generateADTs(it, tempSet, vars, length);
             for (auto & js : tempSet) {
		Expr tempExpr = js;
		//var_counter = 0;
                for (auto & jt : vars) {
                   bool stopCondition = true;
		   while (stopCondition) {
                      Expr type = jt->last()->last();
		      //outs() << "variable type is: " << type << '\n';
		      Expr newVar = spawnVar(type);
		      //outs() << "Before replace one\n";
		      auto resRep = replaceOne(tempExpr, jt, newVar);
		      tempExpr = resRep.first;
		      stopCondition = resRep.second;
		      //outs() << "In while loop, expr is " << tempExpr << '\n';
		   }
		   //outs() << "Exiting while loop\n";
		}
		generatedTerms.insert(tempExpr);
	     }
	     //outs() << "Before copy\n";
             //generatedTerms.insert(finalSet.begin(), finalSet.end());
	     //outs() << "After copy\n";
          }
       }
       //for (auto it = generatedTerms.begin(); it != generatedTerms.end(); it++) {outs() << "  generated list: " << *it << '\n';}
       //generateTermsMemoize(startSet, vars, generatedTerms, result);
       return generatedTerms;
    }

    void generateADTs(Expr templateExp, ExprSet & newTerms, ExprSet & vars, int depth) {
       //templateExp should be FDECL of ind cons
       //newTerms should only contain FAPP of base cons
       //outs() << "DEPTH IS: " << depth << "\n";
       if (depth == 0) {
	  templateFdecl = templateExp;
          return;
       }
       //is not a composite ADT
       /*getComposites();
       if (!compositeConstructors.empty()) {
          auto pos = compositeConstructors.find(templateExp);
	  if (pos != compositeConstructors.end()) {return;}
       }*/
       //var_counter = 0;
       ExprVector fappArgs;
       fappArgs.push_back(templateExp);
       vector<ExprVector> memo;
       memo.push_back(fappArgs);
       vector<ExprVector> newMemo;
       if (vars.empty()) {
          for (int i = 1; i < templateExp->arity()-1; i++) {
             if (templateExp->arg(i) != templateExp->last()) {
                Expr var = bind::mkConst(mkTerm<string>("_o_" + to_string(i), efac), templateExp->arg(i));
		vars.insert(var);
	     }
	  }
       }
       auto iter = vars.begin();
       for (int i = 1; i < templateExp->arity()-1; i++) {
          for (auto & it : memo) {
             //current arg has recursive ADT type
             if (templateExp->arg(i) == templateExp->last()) {
                for (auto & is : newTerms) {
                   ExprVector temp(it.begin(), it.end());
		   //outs() << "is in case 1 is: " << is << '\n';
		   //outs() << "it in case 1 is: " << mknary<FAPP>(temp) << '\n';
                   temp.push_back(is);
                   newMemo.push_back(temp);
                   //outs() << "RESULT OF CASE 1: " << mknary<FAPP>(temp) << "\n";
                }
             }
             //current arg has other ADT type
	     else if (find(types.begin(), types.end(), templateExp->arg(i)) != types.end()) {
		isNestedType = true;
		Expr type = templateExp->arg(i);
		//outs() << "Nested type " << type << endl;
                ExprSet newStartSet;
		ExprSet newVars;
		Expr newBase = mk<FAPP>(*find_if(constructors.begin(), constructors.end(), [type](Expr x){return (x->arity() == 2 && x->last() == type);}));
		//outs() << "New base is " << newBase << endl;
                Expr newTemplate = *find_if(constructors.begin(), constructors.end(), [type](Expr x){return (x->arity() > 2 && x->last() == type);});
		//outs() << "New template is " << newTemplate << endl;
		newStartSet.insert(newBase);
		generateADTs(newTemplate, newStartSet, newVars, disproofDepth);
		for (auto & nss : newStartSet) {
		   Expr tempExpr = nss;
                   //outs() << "Nested term is " << nss << endl;
		   ExprVector temp(it.begin(), it.end());
                   for (auto & jt : newVars) {
                      bool stopCondition = true;
		      while (stopCondition) {
                         Expr type = jt->last()->last();
		         //outs() << "variable type is: " << type << '\n';
		         Expr newVar = spawnVar(type);
		         //outs() << "Before replace one\n";
		         auto resRep = replaceOne(tempExpr, jt, newVar);
		         tempExpr = resRep.first;
		         stopCondition = resRep.second;
		         //outs() << "In while loop, expr is " << tempExpr << '\n';
		      }
		      //outs() << "Exiting while loop\n";
		   }
		   temp.push_back(tempExpr);
		   newMemo.push_back(temp);
		}
	        	
	     }
	     //otherwise
             else {
		outs() << "type is: " << templateExp->arg(i) << '\n';
                ExprVector temp(it.begin(), it.end());
		Expr var = *iter;
		if (iter == vars.end()) {iter = vars.begin();}
		else {iter++;}
                temp.push_back(var);
                newMemo.push_back(temp);
                //outs() << "RESULT OF CASE 2: " << mknary<FAPP>(temp) << "\n";
             }
          }
          memo.assign(newMemo.begin(), newMemo.end());
          newMemo.clear();
       }
       //turn each element of memo to FAPP
       for (auto & it : memo) {
          Expr temp = mknary<FAPP>(it);
	  /*for (auto & jt : vars) { //code for making unique variables
             bool stopCondition = true;
	     outs() << "Before the loop\n";
	     while (stopCondition) {
		Expr newVar = spawnVar(jt->last()->last());
                auto res = replaceOne(temp, jt, newVar);
		temp = res.first;
		stopCondition = res.second;
	     }
	     outs() << "After the loop\n";
	  }*/

	  //outs() << "new term in generateADTs is " << temp << '\n';
          newTerms.insert(temp);
       }
       generateADTs(templateExp, newTerms, vars, depth-1);

    }

    Expr nestedADTHandler(const Expr & e, const Expr & templateExp) { //mark for delete
       bool isNested = false;
       Expr type;
       //outs() << "e is: " << e << '\n';
       //outs() << "templateExp is: " << templateExp << '\n';
       for (auto & it : constructors) {
          for (int i = 1; i < templateExp->arity()-1; i++) {
	     //outs() << "Current it is " << it << '\n';
	     //outs() << "Current arg is " << templateExp->arg(i) << '\n';
	     if (it->arity() <= 2) {continue;}
             if (templateExp->arg(i) == it->last() && templateExp->arg(i) != templateExp->last()) {
		//if (find_if(blockedTypes.begin(), blockedTypes.end(), [it](Expr x){return x == it->first;}) != blockedTypes.end()) {continue;}
                isNested = true;
		type = it;
		outs() << "Nested fdecl is: " << type << '\n';
		blockedTypes.push_back(type);
		outs() << "The adt is nested\n";
		break;
	     }
	  }
       }
       if (!isNested) {outs() << "The adt is NOT nested\n"; return nullptr;}
       ExprVector vars;
       ExprSet tempVars;
       filter(e, bind::IsConst(), inserter(vars, vars.begin()));
       ExprSet generatedTerms;
       auto base = mk<FAPP>(*find_if(constructors.begin(), constructors.end(), [type](Expr x){return (x->arity() == 2 && x->last() == type->last());}));
       generatedTerms.insert(base);
       Expr saveTemplate = templateFdecl;
       generateADTs(type, generatedTerms, tempVars, 3);
       if (generatedTerms.empty()) {outs() << "No terms generated\n";}
       templateFdecl = saveTemplate;
       ExprVector termCollection;
       for (auto & v : vars) {
          for (auto & term : generatedTerms) {
             outs() << "generate term is: " << term << '\n';
	     Expr eq = mk<EQ>(v, term);
	     outs() << "construction step 1 is: " << eq << '\n';
	     termCollection.push_back(eq);
          }
       }
       Expr disjunction = disjoin(termCollection, efac);
       outs() << "construction step 2 is: " << disjunction << '\n';
       return mk<AND>(e, disjunction);
    }

    pair<Expr,bool> replaceOne(const Expr& e, const Expr& from, const Expr& to) {
      ExprVector args;
      if (e == from) {return make_pair(to, true);}
      if (e->arity() == 0) {return make_pair(e, false);}

      bool didrepl = false;
      for (int i = 0; i < e->arity(); i++) {
        if (!didrepl) {
          auto ret = replaceOne(e->arg(i), from, to);
          if (ret.second) {didrepl = true;}
          args.push_back(ret.first);
        }
        else {args.push_back(e->arg(i));}
      }
      return make_pair(mknary(e->op(), args.begin(), args.end()), didrepl);
    }

    Expr spawnVar(const Expr& type) {
       Expr var = bind::mkConst(mkTerm<string>("_t_" + to_string(var_counter), efac), type);
       var_counter++;
       return var;
    }

    Expr getADTType(Expr exp) {
       Expr temp = exp; //exp should be FAPP of constructor
       while (temp != NULL) {
          temp = temp->last();
	  if (temp == NULL) {return NULL;}
          if (isOpX<FDECL>(temp)) {
	     return temp->last();
          }
       }
       return NULL;
    }

    bool testIsomorphism(Expr exp1, Expr exp2) {
       if (exp1 == nullptr && exp2 == nullptr) {return true;}
       if (exp1 == nullptr || exp2 == nullptr) {return false;}
       ExprVector vars;
       ExprMap matching;
       filter(exp1, bind::IsConst(), inserter(vars, vars.begin()));
       for (auto it = vars.begin(); it != vars.end();) {
           if (find(baseconstrapps.begin(), baseconstrapps.end(), *it) == baseconstrapps.end()) {++it;}
           else {it = vars.erase(it);}
       }
       if (findMatching(exp1, exp2, vars, matching)) {
          //outs() << string(sp, ' ') << "expressions are isomorphic\n";
          return true;
       }
       return false;
    }


    void getComposites() {
       //pass 1, collect types
       ExprSet es;
       for (auto & it : constructors) {es.insert(it->last());}
       //pass 2 compare input types to output types
       //if a type is an ADT that is not a recursive call then add to composites
       for (auto & it : constructors) {
	  auto output_type = it->last();
          for (int i = 1; i < it->arity() - 1; i++) {
             auto input_type = it->arg(i);
	     if (input_type == output_type) {continue;}
	     auto res = es.find(input_type);
	     if (res != es.end()) {compositeConstructors.insert(it);}
	  }
       }
    }

    bool syntaxTransformation1(Expr inp, Expr & res) {
	if (isOpX<NEQ>(inp) || isOpX<EQ>(inp)) {
           auto leftTerm = inp->left();
           auto rightTerm = inp->right();
	   ExprVector leftArgs_;
	   ExprVector rightArgs_;
	   ExprVector leftArgs;
	   ExprVector rightArgs;
	   function<bool(Expr)> varTest = [this](Expr x) {
             //outs() << "CURRENT VAR IS: " << x << "\n";
             for (int i = 0; i < baseconstrapps.size(); i++) {
		//outs() << "BASE IS: " << baseconstrapps[i] << '\n';
                if (baseconstrapps[i] == x) {outs() << "EQUALITY\n"; return false;}
	     }
	     return true;
	   };
           //outs() << string(sp+2, ' ') << "LEFT TERM IS: " << leftTerm << '\n';
           //outs() << string(sp+2, ' ') << "RIGHT TERM IS: " << rightTerm << '\n'; 
           filter(leftTerm, bind::IsConst(), inserter(leftArgs_, leftArgs_.begin()));
	   filter(rightTerm, bind::IsConst(), inserter(rightArgs_, rightArgs_.begin()));
	   //outs() << string(sp+2, ' ') << '[';
	   //for (auto & it : leftArgs_) {outs() << it << ", ";}
	   //outs() << "]\n";
	   //outs() << string(sp+2, ' ') << '[';
	   //for (auto & it : rightArgs_) {outs() << it << ", ";}
	   //outs() << "]\n";
           for (int i  = 0; i < leftArgs_.size(); i++) {
              bool hit = false;
              for (int j = 0; j < baseconstrapps.size(); j++) {
                 if (leftArgs_[i] == baseconstrapps[j]) {hit = true; break;}
	      }
	      if (!hit) {leftArgs.push_back(leftArgs_[i]);}
	   }
	   for (int i = 0; i < rightArgs_.size(); i++) {
              bool hit = false;	      
              for (int j = 0; j < baseconstrapps.size(); j++) {
                 if (rightArgs_[i] == baseconstrapps[j]) {hit = true; break;}
	      }
	      if (!hit) {rightArgs.push_back(rightArgs_[i]);}
	   }
	   /*outs() << string(sp+2, ' ') << '[';
	   for (auto & it : leftArgs) {outs() << it << ", ";}
	   outs() << "]\n";
	   outs() << string(sp+2, ' ') << '[';
	   for (auto & it : rightArgs) {outs() << it << ", ";}
	   outs() << "]\n";*/
	   if (leftArgs.size() != rightArgs.size()) {return false;}
	   if (leftArgs.empty() && rightArgs.empty()) {
              res = inp;
	      return true;
	   }
	   if (isNestedType) {
              res = inp;
	      return true;
	   }
           //test if arg sizes are disequal

	   //build disjunction
	   ExprVector disequals;
	   for (int i = 0; i < leftArgs.size(); i++) {
              Expr diseq = mk<NEQ>(leftArgs[i], rightArgs[i]);
	      disequals.push_back(diseq);
	   }
	   Expr disjunction = disjoin(disequals, efac);
	   //outs() << string(sp+2, ' ') << "Final term: " << disjunction << '\n';
	   res = disjunction;
	   return true;
	}
	res = inp;
	return true;
    }

    Expr syntaxTransformation2(Expr e) {
       //two cases: natural numbers or lists
       bool isNat = false;
       if (isOpX<OR>(e)) {
          //break appart disjunction
	  ExprSet dsjs;
	  ExprVector newTerms;
	  getDisj(e, dsjs);
	  for (auto & it : dsjs) {
             Expr leftE = it->left();
	     Expr rightE = it->right();
	     Expr leftType = getADTType(leftE);
	     Expr rightType = getADTType(rightE);
	     if (find(types.begin(), types.end(), leftType) == types.end()) { //case of non-recursive type
                //outs() << "it is " << it << '\n';
		newTerms.push_back(it);
	     }
	     for (auto & is : naturalNumbers) { //is current term a natural number?
                //outs() << "current type is " << leftType << '\n';
                if (is->last() == leftType) {
		   //outs() << "leftE is a natural number\n";
                   isNat = true;
		   break;
	        }
	     }
	     if (isNat) { //yes, the current term is natural
                Expr leftInt = naturalToPresburger(leftE);
		Expr rightInt = naturalToPresburger(rightE);
		newTerms.push_back(mk<NEQ>(leftInt, rightInt));
		isNat = false;
	     }
	     else { //no, we still have a recursive type
                Expr newExpr = syntaxTransformation2(it);
		if (newExpr == NULL) {return NULL;}
		//outs() << "newExpr is " << newExpr << '\n';
		newTerms.push_back(newExpr);
	     }
	  }
	  ExprSet newTermsSet(newTerms.begin(), newTerms.end());
          return disjoin(newTermsSet, efac);
       }
       if (isOpX<EQ>(e) || isOpX<NEQ>(e)) {
          Expr leftE = e->left();
	  Expr rightE = e->right();
	  if (leftE->arity() == 1 && rightE->arity() == 1) {return e;}
	  //outs() << "right term is " << rightE << '\n';
	  //outs() << "left term is " << leftE << '\n';
	  Expr leftType = getADTType(leftE);
	  Expr rightType = getADTType(rightE);
	  ExprVector leftNestedTerms;
	  ExprVector rightNestedTerms;
	  for (auto & it : naturalNumbers) {
             //outs() << "current type is " << leftType << '\n';
             if (it->last() == leftType) {
		//outs() << "leftE is a natural number\n";
                isNat = true;
		break;
	     }
	  }
	  if (isNat) {
             Expr leftInt = naturalToPresburger(leftE);
	     Expr rightInt = naturalToPresburger(rightE);
	     leftNestedTerms.push_back(leftInt);
	     rightNestedTerms.push_back(rightInt);
	     isNat = false;
	  }
	  //handle lhs
	  for (int i = 0; i < leftE->arity(); i++) {
             Expr currentArg = leftE->arg(i);
	     Expr currentType = getADTType(currentArg);
             //outs() << "\tSymbol in left term is: " << currentArg << '\n';
	     //outs() << "\tType of symbol: " << currentType << '\n';
	     //outs() << "\tTop type is: " << leftType << '\n';
	     if (currentType != leftType) {
                /*if (find(types.begin(), types.end(), currentType) != types.end()) {
                   leftNestedTerms.push_back(currentArg);
		}*/
		if (!isOpX<FDECL>(currentArg)) {leftNestedTerms.push_back(currentArg);}
	     }
	     else {
                leftE = currentArg;
		i = -1;
	     }
	  }
	  //for (auto & it : leftNestedTerms) {outs() << "left terms are: " << it << '\n';}
	  //handle rhs
	  for (int i = 0; i < rightE->arity(); i++) {
             Expr currentArg = rightE->arg(i);
	     Expr currentType = getADTType(currentArg);
             //outs() << "\tSymbol in right term is: " << currentArg << '\n';
	     //outs() << "\tType of symbol: " << currentType << '\n';
	     //outs() << "\tTop type is: " << leftType << '\n';
	     if (currentType != rightType) {
                /*if (find(types.begin(), types.end(), currentType) != types.end()) {
                   rightNestedTerms.push_back(currentArg);
		}*/
		if(!isOpX<FDECL>(currentArg)) {rightNestedTerms.push_back(currentArg);}
	     }
	     else {
                rightE = currentArg;
		i = 0;
	     }
	  }
	  //for (auto & it : rightNestedTerms) {outs() << "right terms are: " << it << '\n';}
	  //recombine lhs and rhs
	  if (rightNestedTerms.size() != leftNestedTerms.size()) {return NULL;}
	  ExprVector recombination;
	  for (int i = 0; i < leftNestedTerms.size(); i++) {
             auto tempExpr = mk<NEQ>(leftNestedTerms[i], rightNestedTerms[i]);
	     recombination.push_back(tempExpr);
	  }
	  Expr result = disjoin(recombination, efac);
	  outs() << string(sp + 2, ' ') << "Recombined term is: " <<  result << '\n';
	  return syntaxTransformation2(result);
       }
       return e;
    }

    ExprVector getNaturalNumbers() {
       ExprVector nats;
       ExprVector natTypes;
       for (auto & it : constructors) {
          //outs() << "arity of constructor "<< it  << " is " << it->arity() << '\n';
	  if (it->arity() == 3) {
             bool isSameType = true;
             for (int i = 1; i < it->arity(); i++) {
                //outs() << "argument is " << it->arg(i) << '\n';
		if (it->arg(i) != it->last()) {isSameType = false;}
	     }
	     if (isSameType) {
                natTypes.push_back(it->last());
	     }
	  }
       }
       for (auto & it : natTypes) {
          for (auto & is : constructors) {
             if (is->last() == it) {
                nats.push_back(is);
	     }
	  }
       }
       return nats;
    }

    Expr naturalToPresburger(Expr & exp) {
       Expr e = exp;
       int count = 0;
       if (e->arity() == 1) {return mkMPZ(0, efac);}
       //outs() << "e is " << e << '\n';
       if (isOpX<FAPP>(e)) {
          for (int i = 0; i < e->arity(); i++) {
             //outs() << "ith arg is " << e->arg(i) << '\n';
	     if (isOpX<FDECL>(e->arg(i))) {
                if (e->arg(i)->arity() == 3) {
                   count++;
		}
                else {break;}
	     }
	     if (isOpX<FAPP>(e->arg(i))) {
                e = e->arg(i);
		i = -1;
		//outs() << "e is now " << e << '\n';
	     }
	  }
	  //outs() << "count is " << count << '\n';
	  return mkMPZ(count, efac);
       }
       return e;
    }

    //end of disproof section

    bool proveByContradiction (Expr subgoal)
    {
      auto assumptionsTmp = assumptions;
      uniquePushConj(mkNeg(subgoal), assumptions);
      bool res = false;
      eliminateEqualities(subgoal);
      if (mergeAssumptions(1))
      {
        res = true;
        if (verbose) outs () << string(sp, ' ') << "proven by contradiction\n";
      }
      assumptions = assumptionsTmp;
      return res;
    }

    bool splitByGoal (Expr subgoal)
    {
      // heuristically pick a split (currently, one predicate)
      ExprSet dsjs;
      getDisj(subgoal, dsjs);
      if (dsjs.size() < 2) return false;

      auto spl = dsjs.end();
      for (auto it = dsjs.begin(); it != dsjs.end(); ++it)
      {
        for (auto & a : assumptions)
        {
          if (contains (a, *it))
          {
            if (isOp<ComparissonOp>(*it)) spl = it;  // try to find a comparisson
            if (*spl == NULL) spl = it;              // if none, find any
          }
        }
      }
      if (spl == dsjs.end()) spl = dsjs.begin();
      if (verbose) outs() << string(sp, ' ') << "deciding: " << **spl << "\n";

      auto rewriteHistoryTmp = rewriteHistory;
      auto rewriteSequenceTmp = rewriteSequence;
      auto assumptionsTmp = assumptions;

      uniquePushConj(mkNeg(*spl), assumptions);
      eliminateEqualities(subgoal);
      if (mergeAssumptions())
      {
        assumptions = assumptionsTmp;
        return true;
      }
      printAssumptions();

      dsjs.erase(spl);
      subgoal = disjoin(dsjs, efac);
      if (verbose) outs() << string(sp, ' ') << "current subgoal: " << *subgoal << "\n";

      if (verbose) outs () << string(sp, ' ') << "{\n";
      sp += 2;
      bool res = rewriteAssumptions(subgoal);
      sp -= 2;
      if (verbose) outs () << string(sp, ' ') << "}\n";

      rewriteHistory = rewriteHistoryTmp;
      rewriteSequence = rewriteSequenceTmp;
      assumptions = assumptionsTmp;
      if (res)
      {
        if (verbose) outs () << string(sp, ' ') << "succeeded\n";
        return true;
      }

      return false;
    }

    // potentially useful heuristic
    bool similarityHeuristic (Expr subgoal)
    {
      // heuristically pick a split: first, using disjunctions
      ExprSet cands;
      for (auto & a : assumptions)
      {
        if (isOpX<OR>(a))
        {
          ExprSet dsjs;
          getDisj(a, dsjs);
          if (dsjs.size() < 2) continue;
          auto it = dsjs.begin();
          for (; it != dsjs.end(); ++it)
          {
            if (*it == subgoal)
            {
              it = dsjs.erase(it);
              cands.insert(disjoin(dsjs, efac));
              break;
            }
          }
        }
      }
      if (cands.empty())      // then, based on matching
      {
        ExprVector args;
        filter(subgoal, bind::IsConst (), inserter(args, args.begin()));
        for (auto & a : assumptions)
        {
          if (isOpX<FORALL>(a)) continue;

          ExprMap matching;
          if (findMatching (subgoal, a, args, matching))
          {
            ExprSet eqs;
            for (auto & m : matching)
              if (m.first != m.second)
                eqs.insert(mk<EQ>(m.first, m.second));
            cands.insert(mkNeg(conjoin(eqs, efac)));
          }
        }
        if (cands.empty()) return false;
      }

      bool changed = false;
      for (auto & c : cands)
      {
        bool redund = false;
        for (auto & a : assumptions)
        {
          if (isOpX<FORALL>(a)) continue;
          if (u.implies(a, c))
          {
            redund = true;
            break;
          }
        }
        if (redund) continue;
        uniquePushConj(c, assumptions);
        changed = true;
      }
      if (!changed) return false;

      if (mergeAssumptions())
      {
        return true;
      }
      printAssumptions();

      if (verbose) outs () << string(sp, ' ') << "current subgoal: " << *subgoal << "\n";
      if (verbose) outs () << string(sp, ' ') << "{\n";
      sp += 2;
      bool res = rewriteAssumptions(subgoal);
      sp -= 2;
      if (verbose) outs () << string(sp, ' ') << "}\n";

      return res;
    }

    bool splitDisjAssumptions (Expr subgoal)
    {
      // more like a brute force splitting
      set<ExprSet> cands;
      map<ExprSet, Expr> origAssms;
      for (auto it = assumptions.begin(); it != assumptions.end(); )
      {
        Expr a = *it;
        if (find (blockedAssms.begin(), blockedAssms.end(), *it) != blockedAssms.end())
        {
          it = assumptions.erase(it);
          continue;
        }
        if (isOpX<ITE>(a))
        {
          a = mk<OR>(mk<AND>(a->left(), a->right()),
                     mk<AND>(mkNeg(a->left()), a->last()));
        }
        a = simplifyBool(simplifyArr(a));
        if (isOpX<OR>(a))
        {
          ExprSet dsjs;
          getDisj(a, dsjs);
          if (dsjs.size() < 2) continue;
          cands.insert(dsjs);
          origAssms[dsjs] = *it;
        }
        ++it;
      }

      if (cands.empty()) return false;
      ExprSet spl = *cands.begin();

      if (spl.empty()) return false;

      blockedAssms.push_back(origAssms[spl]);

      int part = 1;
      bool res = true;

      auto subgoalTmp = subgoal;
      auto assumptionsTmp = assumptions;
      auto rewriteHistoryTmp = rewriteHistory;
      auto rewriteSequenceTmp = rewriteSequence;

      for (auto & s : spl)
      {
        if (verbose) outs () << string(sp, ' ') << "split for (part " << part << "/"
            << spl.size()<< "): " << *s << "\n" << string(sp, ' ') << "{\n";
        sp += 2;
        part++;

        uniquePushConj(s, assumptions);
        eliminateEqualities(subgoal);
        if (mergeAssumptions())
        {
          assumptions = assumptionsTmp;
          sp -= 2;
          if (verbose) outs () << string(sp, ' ') << "}\n";
          continue;
        }
        for (auto it = assumptions.begin(); it != assumptions.end(); ++it)
        {
          if (origAssms[spl] == *it)
          {
            assumptions.erase(it);
            break;
          }
        }
        printAssumptions();

        res = rewriteAssumptions(subgoal);
        sp -= 2;
        if (verbose) outs () << string(sp, ' ') << "}\n";

        rewriteHistory = rewriteHistoryTmp;
        rewriteSequence = rewriteSequenceTmp;
        assumptions = assumptionsTmp;
        subgoal = subgoalTmp;
        if (!res) break;
      }

      blockedAssms.pop_back();
      if (res)
      {
        if (verbose) outs () << string(sp, ' ') << "splitting succeeded\n";
        return true;
      }
      else
      {
        if (verbose) outs () << string(sp, ' ') << "unable to succeed\n";
        return false;
      }
    }

    // preprocessing of the main goal
    void unfoldGoal()
    {
      ExprVector goalArgs;
      Expr unfoldedGoalQF = goal->last();
      bool toRebuild = false;
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        //   - classify constructors for all ADTs that appear in the goal
        Expr type = goal->arg(i)->last();
        for (auto & a : constructors)
        {
          if (a->last() == type)
          {
            bool ind = false;
            for (int i = 0; i < a->arity() - 1; i++)
            {
              if (a->last() == a->arg(i))
              {
                ind = true;
                if (indConstructors[type] != NULL && indConstructors[type] != a)
                {
                  outs () << "Several inductive constructors are not supported\n";
                  exit(1);
                }
                indConstructors[type] = a;
              }
            }
            if (!ind)
            {
              if (baseConstructors[type] != NULL && baseConstructors[type] != a)
              {
                outs () << "Several base constructors are not supported\n";
                exit(1);
              }
              baseConstructors[type] = a;
              baseconstrapps.push_back(fapp(a));
            }
          }
        }

        //   - replace all non-inductive ADTs
        if (baseConstructors[type] != NULL && indConstructors[type] == NULL)
        {
          toRebuild = true;
          ExprVector args;
          args.push_back(baseConstructors[type]);
          for (int i = 1; i < baseConstructors[type]->arity() - 1; i++)
          {
            // TODO: make sure the name is unique
            Expr s = bind::mkConst(mkTerm<string>
                         ("_b_" + to_string(glob_ind++), efac),
                         baseConstructors[type]->arg(i));
            goalArgs.push_back(s->last());
            args.push_back(s);
          }
          Expr newApp = mknary<FAPP>(args);
          unfoldedGoalQF = replaceAll(unfoldedGoalQF, bind::fapp(goal->arg(i)), newApp);
        }
        else
        {
          goalArgs.push_back(goal->arg(i));
        }
      }

      // classify functions; TODO: avoid repetitions

      map<Expr, int> occs;
      getCommonSubterms(conjoin(assumptions, efac), occs);
      ExprSet funs;
      for (auto & m : occs)
        if (isOpX<FAPP>(m.first) && m.first->left()->arity() > 2 &&
          find(constructors.begin(), constructors.end(), m.first->left()) == constructors.end())
            funs.insert(m.first->left());

      for (auto & f : funs)
      {
        ExprVector assmsWith;
        for (auto & a : assumptions)
          if (contains(a, f))
            assmsWith.push_back(a);

        if (assmsWith.size() != 1) continue;
        // replace all non-recursive functions

        ExprVector result;
        if (useAssumption(unfoldedGoalQF, assmsWith[0], result, true))
        {
          unfoldedGoalQF = result[0];
          toRebuild = true;
        }
      }

      if (toRebuild)
      {
        goalArgs.push_back(unfoldedGoalQF);
        goal = mknary<FORALL>(goalArgs);

        // continue recursively, because newly introduced vars/funs may again need unfolding
        unfoldGoal();
      }
    }

    // and to enable searching for RHS of assumptions
    void insertSymmetricAssumption(Expr assm)
    {
      if (isOpX<EQ>(assm))
      {
        assumptions.push_back(mk<EQ>(assm->right(), assm->left()));
      }
      else if (isOpX<FORALL>(assm) && isOpX<EQ>(assm->last()))
      {
        ExprVector args;
        for (int i = 0; i < assm->arity() - 1; i++) args.push_back(assm->arg(i));
        args.push_back(mk<EQ>(assm->last()->right(), assm->last()->left()));
        assumptions.push_back(mknary<FORALL>(args));
      }
    }

    void printAssumptions()
    {
      if (!verbose) return;
      outs () << string(sp, ' ') << "{\n";
      outs () << string(sp+2, ' ') << string(20, '=') << "\n";
      for (int i = 0; i < assumptions.size(); i++)
      {
        outs () << string(sp+2, ' ') << "| Assumptions [" << i << "]: ";
        pprint(assumptions[i]);
      }
      outs () << string(sp+2, ' ') << string(20, '=') << "\n";
      outs () << string(sp, ' ') << "}\n";
    }

    bool induction(int num)
    {
      assert(num < goal->arity() - 1);
      Expr typeDecl = goal->arg(num);
      Expr type = goal->arg(num)->last();

      Expr baseConstructor = baseConstructors[type];
      Expr indConstructor = indConstructors[type];

      // instantiate every quantified variable (except the inductive one) in the goal
      Expr goalQF = goal->last();
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        if (i == num) continue;
        // TODO: make sure the name is unique
        Expr s = bind::mkConst(mkTerm<string> ("_v_" + to_string(glob_ind), efac), goal->arg(i)->last());
        glob_ind++;
        goalQF = replaceAll(goalQF, bind::fapp(goal->arg(i)), s);
      }

      // prove the base case
      Expr baseSubgoal = replaceAll(goalQF, typeDecl, baseConstructor);
      ExprVector assumptionsTmp = assumptions;
      if (isOpX<IMPL>(baseSubgoal))
      {
        assumptions.push_back(baseSubgoal->left());
        baseSubgoal = baseSubgoal->right();
      }

      if (verbose)
      {
        outs() << "\nBase case:       ";
        pprint(baseSubgoal);
        outs() << "\n{\n";
      }

      tribool baseres = simpleSMTcheck(baseSubgoal);
      if (baseres)
      {
        if (verbose) outs() << "  proven trivially\n";
      }
      else
      {
        eliminateEqualities(baseSubgoal);
        if (mergeAssumptions())
        {
          if (verbose) outs() << "  proven trivially\n";
          baseres = true;
          assumptions = assumptionsTmp;
        }
        else
        {
          splitAssumptions();
          printAssumptions();

          rewriteHistory.clear();
          rewriteSequence.clear();

          baseres = rewriteAssumptions(baseSubgoal);
        }
      }

      if (verbose) outs () << "}\n";
      if (!baseres) baseres = doCaseSplitting(baseSubgoal);
      if (!baseres) return false;

      if (!assumptionsTmp.empty()) assumptions = assumptionsTmp;

      // generate inductive hypotheses
      ExprVector args;
      ExprVector indHypotheses;
      bool allQF = true;
      for (int i = 1; i < indConstructor->arity() - 1; i++)
      {
        // TODO: make sure the name is unique
        Expr s;
        Expr singleCons = NULL;
        for (auto & a : constructors)
        {
          if (a->last() == indConstructor->arg(i))
          {
            if (singleCons != NULL)
            {
              singleCons = NULL;
              break;
            }
            singleCons = a;
          }
        }
        if (singleCons != NULL)
        {
          // unfold definitions, if possible
          ExprVector argsCons;
          for (int j = 1; j < singleCons->arity() - 1; j++)
          {
            argsCons.push_back(bind::mkConst(mkTerm<string> ("_t_" + to_string(glob_ind), efac), singleCons->arg(j)));
            glob_ind++;
          }
          s = bind::fapp (singleCons, argsCons);
        }
        else
        {
          s = bind::mkConst(mkTerm<string> ("_t_" + to_string(glob_ind), efac), indConstructor->arg(i));
          glob_ind++;
        }

        args.push_back(s);

        if (type == indConstructor->arg(i)) // type check
        {
          ExprVector argsIH;
          for (int j = 0; j < goal->arity() - 1; j++)
          {
            if (j != num) argsIH.push_back(goal->arg(j));
          }
          argsIH.push_back(replaceAll(goal->last(), bind::fapp(typeDecl), s));
          if (argsIH.size() == 1)
          {
            indHypotheses.push_back(argsIH.back());
          }
          else
          {
            allQF = false;
            indHypotheses.push_back(mknary<FORALL>(argsIH));
          }
        }
      }
      for (auto & a : indHypotheses)
      {
        assumptions.push_back(a);
        // always add symmetric IH?
        insertSymmetricAssumption(a);
      }
      // prove the inductive step
      Expr indConsApp = bind::fapp(indConstructor, args);
      Expr indSubgoal = replaceAll(goalQF, bind::fapp(typeDecl), indConsApp);

      if (isOpX<IMPL>(indSubgoal))
      {
        assumptions.push_back(indSubgoal->left());
        indSubgoal = indSubgoal->right();
      }

      eliminateEqualities(indSubgoal);
      if (mergeAssumptions()) return true;
      splitAssumptions();
      if (verbose)
      {
        outs() << "\nInductive step:       ";
        pprint(indSubgoal);
        outs() << "\n{\n";
      }

      rewriteHistory.clear();
      rewriteSequence.clear();

      tribool indres = simpleSMTcheck(indSubgoal);
      if (indres)
      {
        if (verbose) outs() << "  proven trivially\n}\n";
        return true;
      }
      else
      {
        printAssumptions();
        indres = rewriteAssumptions(indSubgoal);
        if (indres)
        {
          if (verbose) outs () << "}\n";
          return true;
        }
      }
      // last resort so far
      return doCaseSplitting(indSubgoal);
    }

    bool doCaseSplitting(Expr goal)
    {
      for (int i = 0; i < assumptions.size(); i++)
      {
        Expr pre;
        auto a = assumptions[i];
        if (isOpX<FORALL>(a) && isOpX<IMPL>(a->last()))
        {
          ExprSet pres;
          getConj(a->last()->left(), pres);

          ExprVector varz;
          for (int i = 0; i < a->arity() - 1; i++) varz.push_back(bind::fapp(a->arg(i)));

          for (auto & p : pres)
          {
            if (emptyIntersect(p, varz))
            {
              pre = p;
              break;
            }
          }
        }

        if (isOpX<IMPL>(a)) pre = a->left();

        if (pre != NULL)
        {
          // GF: to support if isOpX<EQ>(pre) = true.
          Expr d = destructDiseq(pre);
          if (d != NULL)
          {
            assert(isOpX<EQ>(d));
            if (verbose) outs () << string(sp, ' ') << "case splitting for " << *d->left() << ":\n";
            if (verbose) outs () << string(sp, ' ') << "case " << *d << "\n" << string(sp, ' ') << "{\n";
            auto assumptionsTmp = assumptions;
            auto rewriteHistoryTmp = rewriteHistory;
            auto rewriteSequenceTmp = rewriteSequence;
            auto goalTmp = goal;

            goal = replaceAll(goal, d->left(), d->right());
            for (int j = 0; j < assumptions.size(); j++)
            {
              assumptions[j] = simplifyBool(replaceAll(assumptions[j], pre, mk<TRUE>(efac)));
              assumptions[j] = replaceAll(assumptions[j], d->left(), d->right());
            }

            eliminateEqualities(goal);
            mergeAssumptions(1);
            sp += 2;
            printAssumptions();
            if (verbose) outs () << string(sp, ' ') << "current subgoal: " << *goal << "\n";
            bool partiallyDone = rewriteAssumptions(goal);
            sp -= 2;

            assumptions = assumptionsTmp;
            rewriteHistory = rewriteHistoryTmp;
            rewriteSequence = rewriteSequenceTmp;
            goal = goalTmp;

            if (!partiallyDone) continue;
            if (verbose) outs() << string(sp, ' ') << "}\n";

            pre = mkNeg(pre);
            assert(isOpX<EQ>(pre) && pre->left() == d->left());
            if (verbose) outs () << string(sp, ' ') << "case " << *pre << "\n" << string(sp, ' ') << "{\n";

            goal = replaceAll(goal, pre->left(), pre->right());
            for (int j = 0; j < assumptions.size(); j++)
            {
              assumptions[j] = simplifyBool(replaceAll(assumptions[j], pre, mk<TRUE>(efac)));
              assumptions[j] = replaceAll(assumptions[j], pre->left(), pre->right());
            }
            eliminateEqualities(goal);
            mergeAssumptions(1);
            sp += 2;
            printAssumptions();
            if (verbose) outs () << string(sp, ' ') << "current subgoal: " << *goal << "\n";
            bool done = rewriteAssumptions(goal);
            sp -= 2;

            assumptions = assumptionsTmp;
            rewriteHistory = rewriteHistoryTmp;
            rewriteSequence = rewriteSequenceTmp;

            if (done)
            {
              if (verbose) outs() << string(sp, ' ') << "\n}\n";
              return true;
            }
          }
        }
      }
      return false;
    }

    Expr destructDiseq(Expr e)
    {
      if (isOpX<NEG>(e))
      {
        e = mkNeg(e->left());
      }
      if (isOp<NEQ>(e))
      {
        Expr ty;
        if (bind::isAdtConst(e->left()))
        {
          ty = e->left()->last()->last();
        }
        else if (bind::isAdtConst(e->right()))
        {
          ty = e->right()->last()->last();
        }

        if (ty == NULL) return NULL;

        Expr t;
        if (e->right()->last() == baseConstructors[ty])
        {
          t = e->left();
        }
        else if (e->left()->last() == baseConstructors[ty])
        {
          t = e->right();
        }

        Expr indConstructor = indConstructors[ty];
        ExprVector args;
        for (int i = 1; i < indConstructor->arity() - 1; i++)
        {
          // TODO: make sure the name is unique
          Expr s = bind::mkConst(mkTerm<string> ("_t_" + to_string(glob_ind), efac), indConstructor->arg(i));
          glob_ind++;
          args.push_back(s);
        }
        Expr indConsApp = bind::fapp(indConstructor, args);
        return mk<EQ>(t, indConsApp);
      }

      return NULL;
    }

    tribool solveNoind(int do_rewrite = true, int rounds = 2)
    {
      if (do_rewrite)
      {
        if (simpleSMTcheck(goal))
        {
          if (verbose) outs () << "Proved (with Z3)\n";
          return true;
        }
        splitAssumptions();
        eliminateEqualities(goal);
        auto assumptionsTmp = assumptions;
        mergeAssumptions(rounds);
        eliminateEqualities(goal);
        printAssumptions();
        if (verbose) outs () << "=====\n" << *goal << "\n\n\n";
        if (rewriteAssumptions(goal))
        {
          if (verbose) outs () << "\nProved\n";
          return true;
        }
        // revert and try induction:
        assumptions = assumptionsTmp;
      }

      ExprSet qFreeAssms;
      for (auto it = assumptions.begin(); it != assumptions.end(); )
      {
        if (!isOpX<FORALL>(*it))
        {
          if (isOpX<EQ>(*it) || isOpX<NEQ>(*it) || isOpX<FAPP>(*it) || isOpX<NEG>(*it) || isOpX<SELECT>(*it)) // super big hack
            qFreeAssms.insert(*it);

          it = assumptions.erase(it);
        }
        else ++it;
      }

      if (verbose) outs () << "\nProving by induction\n";
      goal = createQuantifiedFormula(mk<IMPL>(conjoin(qFreeAssms, efac), goal), constructors);
      if (isOpX<FORALL>(goal)) return solve();
      else return false;
    }

    tribool solve()
    {
      Expr goalPre = goal;
      for (int i = 0; i < 5; i++)
      {
        unfoldGoal();
        if (simplifyGoal())
        {
          if (verbose) outs () << "Trivially Proved\n";
          return true;
        }
        if (goalPre == goal) break;
        goalPre = goal;
      }
      rewriteHistory.push_back(goal);

      if (verbose)
      {
        outs () << "Simplified goal: ";
        pprint(goal);
      }

      //if disproof flag enabled
      if (disproofDepth > 0) {return disproof(goal);}

      //dumpToFile(goal, assumptions);

      for (int i = 0; i < goal->arity() - 1; i++)
      {
        Expr type = goal->arg(i)->last();
        if (baseConstructors[type] != NULL && indConstructors[type] != NULL)
        {
          if (induction(i))
          {
            if (verbose) outs () << "\nProved\n";
            return true;
          }
        }
      }
      tribool res = simpleSMTcheck(goal);
      if (verbose)
      {
        if (res) outs () << "Proved (with Z3)\n";
        else return indeterminate;
      }
      return res;
    }

    tribool simpleSMTcheck(Expr goal)
    {
      if (!useZ3) return false;
      return u.implies(conjoin(assumptions, efac), goal);
    }
  };


  void adtSolve(EZ3& z3, Expr s, int maxDepth,
                int maxGrow, int mergingIts, int earlySplit, bool verbose, int useZ3, int to, int disproofDepth)
  {
    ExprVector constructors;
    for (auto & a : z3.getAdtConstructors()) constructors.push_back(regularizeQF(a));

    ExprVector assumptions;
    Expr goal;

    ExprSet cnjs;
    getConj(s, cnjs);
    for (auto c : cnjs)
    {
      bool possibleGoal = false;
      if (isOpX<NEG>(c) || isOpX<EXISTS>(c))
        possibleGoal = true;

      if (possibleGoal)
      {
        if (goal != NULL)
        {
          errs() << "WARNING: two (or more) asserts that qualify to be a goal."
                 << "\nUsing one of those.\n";
          if (isOpX<FORALL>(goal)) possibleGoal = false;
        }
      }

      if (possibleGoal)
        goal = regularizeQF(mkNeg(c));
      else
        assumptions.push_back(regularizeQF(c));
    }

    if (goal == NULL)
    {
      outs () << "Unable to detect the goal\n";
      return;
    }

    ADTSolver sol (goal, assumptions, constructors, 0, 0, maxDepth, maxGrow, mergingIts, earlySplit, verbose, useZ3, to, disproofDepth);
    //sol.dumpToFile(goal, assumptions);
    tribool res = isOpX<FORALL>(goal) ? sol.solve() : sol.solveNoind();
    outs () << (res ? "unsat\n" : (!res ? "sat\n" : "unknown\n"));
  }
}

#endif
