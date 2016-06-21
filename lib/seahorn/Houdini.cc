#include "seahorn/Houdini.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/HornClauseDB.hh"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

#include "ufo/Expr.hpp"
#include <vector>

using namespace llvm;

namespace seahorn
{
  char Houdini::ID = 0;
  bool Houdini::runOnModule (Module &M)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();

    //load the Horn clause database
    auto &db = hm.getHornClauseDB ();
    db.buildIndexes ();

    workListAlgo(db);
    //getUseRuleSet(db);

    return false;
  }

  void Houdini::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.addRequired<HornifyModule> ();
    AU.setPreservesAll();
  }

  void Houdini::printDB (const HornClauseDB &db)
  {
    outs () << db << "\n";
  }

  void Houdini::printHello ()
  {
    outs () << "Hello there.\n";
  }

  void Houdini::getUseRuleSet(HornClauseDB &db)
  {
	  auto &workList = db.getRules();
	  while (!workList.empty())
	  {
		  HornRule r = workList.front();
		  outs() << "rule head: " << *(r.head()) << "\n";
		  outs() << "rule body: " << *(r.body()) << "\n";
		  outs() << "use size: " << db.use(r.head()).size() << "\n";
		  workList.erase(workList.begin());
	  }
  }

  Expr Houdini::guessCandidate(Expr fdecl)
  {
	ExprVector bvars;
	ExprVector bins;   // a vector of LT expressions
	Expr cand = NULL;

	int bvar_count = 0;
	unsigned i = 0;
	for (i=0; i < bind::domainSz(fdecl); i++)
	{
		// if its type is INT
		if (isOpX<INT_TY>(bind::domainTy(fdecl, i)))
		{
			// what is efac?
			Expr bvar = bind::bvar (i, mk<INT_TY>(bind::domainTy(fdecl, i)->efac())); //the id of bvar is the same as related arg index
			bvars.push_back(bvar);
			bvar_count ++;
		}
	}
	//outs() << "arg_count = " << i << "\n";
	//outs() << "bvar count = " << bvar_count << "\n";

	//What if there's no bvar?
	if(bvar_count == 0)
	{
		cand = mk<TRUE>(fdecl->efac());
	}
	// if there is only one bvar, create a int constant and make an lt expr
	else if(bvar_count == 1)
	{
		Expr zero = mkTerm<mpz_class> (0, fdecl->efac());
		cand = mk<LT>(bvars[0], zero);
	}
	// if there are more than two bvars, make an lt expr
	else if(bvar_count == 2)
	{
		Expr lt1 = mk<LT>(bvars[0], bvars[1]);
		Expr lt2 = mk<LT>(bvars[1], bvars[0]);
		bins.push_back(lt1);
		bins.push_back(lt2);

		cand = mknary<AND>(bins.begin(), bins.end());
	}
	else // bvar_count > 2
	{
		for(int j=0; j<bvars.size()-1; j++)
		{
			Expr lt = mk<LT>(bvars[j], bvars[j+1]);
			bins.push_back(lt);
		}
		cand = mknary<AND>(bins.begin(), bins.end());
	}
	//outs() << *cand << "\n";

	return cand;
  }

  #define SAT true
  #define UNSAT false

  void Houdini::workListAlgo(HornClauseDB &db)
  {
	  auto &workList = db.getRules();
	  while (!workList.empty())
	  {
		  //outs() << "[WORKLIST SIZE]: " << workList.size() << "\n";
		  HornRule r = workList.front();

		  outs() << "[RULE HEAD]: " << *(r.head()) << "\n";
		  outs() << "[RULE BODY]: " << *(r.body()) << "\n";

		  //generate candidate for rule head
		  Expr head_app = r.head();
		  Expr head_pred = bind::fname(head_app);
		  Expr head_cand = guessCandidate(head_pred);

		  //apply head_cand to actual arguments
		  ExprMap head_bvar_map;
		  //I need a visitor here.
		  ExprVector bvars;
		  get_all_bvars(head_cand, std::back_inserter(bvars));

		  for(ExprVector::iterator it = bvars.begin(); it != bvars.end(); ++it)
		  {
			  //outs() << *(*it) << "\n";
			  unsigned bvar_id = bind::bvarId(*it);
			  Expr head_app_arg = bind::domainTy(head_app, bvar_id);// To improve
			  head_bvar_map.insert(std::pair<Expr,Expr>(*it, head_app_arg));
		  }
		  //outs() << "[HEAD BVAR MAP]:\n";
		  //outs() << "[MAP SIZE]: " << head_bvar_map.size() << "\n";
		  //for (ExprMap::iterator it = head_bvar_map.begin(); it!=head_bvar_map.end(); ++it)
		  //{
		  //  outs() << "[KEY]: " << *(it->first) << ", [VALUE]: " << *(it->second) << "\n";
		  //}

		  Expr head_cand_app = replace(head_cand, head_bvar_map);

		  //cand_app is application of the overall conjunction
		  Expr neg_head_cand_app = mk<NEG>(head_cand_app);

		  //outs() << "[NEG HEAD CAND APP]: " << *neg_head_cand_app << "\n";

		  //generate candidate for rule body
		  Expr body = r.body();
		  ExprMap body_map;
		  ExprVector body_pred_app_vec;
		  get_all_pred_apps(body, db, std::back_inserter(body_pred_app_vec));
		  //outs() << "[BODY PRED NUM]: " << body_pred_app_vec.size() << "\n";
		  for (ExprVector::iterator it = body_pred_app_vec.begin(); it != body_pred_app_vec.end(); ++it)
		  {
			  Expr body_pred_app = *it;
			  Expr body_pred = bind::fname(body_pred_app);
			  Expr body_cand = guessCandidate(body_pred);
			  //outs() << "[BODY CAND]: " << *body_cand << "\n";
			  //apply body_cand to actual arguments
			  ExprMap body_bvar_map;
			  ExprVector body_bvars;
			  get_all_bvars(body_cand, std::back_inserter(body_bvars));
			  for(ExprVector::iterator it_bv = body_bvars.begin(); it_bv != body_bvars.end(); ++it_bv)
			  {
				  unsigned bvar_id = bind::bvarId(*it_bv);
				  Expr body_app_arg = bind::domainTy(body_pred_app, bvar_id);// To improve
				  body_bvar_map.insert(std::pair<Expr,Expr>(*it_bv, body_app_arg));
			  }
			  Expr body_cand_app = replace(body_cand, body_bvar_map);
			  //outs() << "[BODY CAND APP]: " << *body_cand_app << "\n";
			  body_map.insert(std::pair<Expr, Expr>(body_pred_app, body_cand_app));
		  }
		  Expr new_body = replace(body, body_map);

		  //outs() << "[NEW BODY]: " << *new_body << "\n";

		  //update cand and cand_app
		  Expr cand_app = mk<AND>(neg_head_cand_app, new_body);

		  outs() << "[CANDIDATE]: " << *cand_app << "\n";

		  if(validateRule(cand_app) == SAT)
		  {
			  //weaken candidate for r.head(), how ?
			  if (isOpX<AND>(head_cand_app) && head_cand_app->arity() > 1)
			  {
				  //add rules in db.use(r.head()) to worklist
				  Expr head_app = r.head();
				  //outs() << "[USE SET SIZE]: " << db.use(head_app).size() << "\n";
				  for(auto r_use : db.use(head_app))
				  {
				  	  workList.push_back(*r_use);
				  }

				  //weaken candidate for r.head()
				  while (validateRule(cand_app) == SAT)
				  {
					  //outs() << "[ARITY]: " << head_cand_app->arity() << "\n";
					  if(head_cand_app->arity() <= 1 || !isOpX<AND>(head_cand_app))
					  {
						  break;
					  }
					  ExprVector new_head_vec;
					  for(auto it = head_cand_app->args_begin (), end = head_cand_app->args_end (); it != end; ++it)
					  {
						  new_head_vec.push_back(*it);
					  }
					  new_head_vec.erase(new_head_vec.begin());
					  if(new_head_vec.size() > 1)
					  {
						  head_cand_app = mknary<AND>(new_head_vec.begin(), new_head_vec.end());
					  }
					  else
					  {
						  head_cand_app = new_head_vec[0];
					  }
					  neg_head_cand_app = mk<NEG>(head_cand_app);
					  //outs() << "[HEAD AFTER WEAKEN]: " << *neg_head_cand_app << "\n";
					  cand_app = mk<AND>(neg_head_cand_app, new_body);
					  outs() << "[CANDIDATE AFTER WEAKEN]: " << *cand_app << "\n";
				  }
			  }
			  else
			  {
				  //what to do?
			  }
			  workList.erase(workList.begin());
		  }
		  else // the ret is UNSAT
		  {
		      workList.erase(workList.begin());
		  }
	  }
  }

  bool Houdini::validateRule(Expr cand_app)
  {
	  outs() << "[CANDIDATE]: " << *cand_app << "\n";
	  // should call smt solver
	  return UNSAT;
  }
}
