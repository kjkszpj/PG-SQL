/*-------------------------------------------------------------------------
 *
 * nodeNestloop.c
 *	  routines to support nest-loop joins
 *
 * Portions Copyright (c) 1996-2011, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/nodeNestloop.c
 *
 *-------------------------------------------------------------------------
 */
/*
 *	 INTERFACE ROUTINES
 *		ExecNestLoop	 - process a nestloop join of two plans
 *		ExecInitNestLoop - initialize the join
 *		ExecEndNestLoop  - shut down the join
 */

#include "postgres.h"

#include "executor/execdebug.h"
#include "executor/nodeNestloop.h"
#include "utils/memutils.h"


/* ----------------------------------------------------------------
 *		ExecNestLoop(node)
 *
 * old comments
 *		Returns the tuple joined from inner and outer tuples which
 *		satisfies the qualification clause.
 *
 *		It scans the inner relation to join with current outer tuple.
 *
 *		If none is found, next tuple from the outer relation is retrieved
 *		and the inner relation is scanned from the beginning again to join
 *		with the outer tuple.
 *
 *		NULL is returned if all the remaining outer tuples are tried and
 *		all fail to join with the inner tuples.
 *
 *		NULL is also returned if there is no tuple from inner relation.
 *
 *		Conditions:
 *		  -- outerTuple contains current tuple from outer relation and
 *			 the right son(inner relation) maintains "cursor" at the tuple
 *			 returned previously.
 *				This is achieved by maintaining a scan position on the outer
 *				relation.
 *
 *		Initial States:
 *		  -- the outer child and the inner child
 *			   are prepared to return the first tuple.
 * ----------------------------------------------------------------
 */
TupleTableSlot *
ExecNestLoop(NestLoopState *node)
{
	NestLoop   *nl;
	PlanState  *innerPlan;
	PlanState  *outerPlan;
	TupleTableSlot *outerTupleSlot;
	TupleTableSlot *innerTupleSlot;
	List	   *joinqual;
	List	   *otherqual;
	ExprContext *econtext;
	ListCell   *lc;

	/*
	 * get information from the node
	 */
	ENL1_printf("getting info from node");

	nl = (NestLoop *) node->js.ps.plan;
	joinqual = node->js.joinqual;
	otherqual = node->js.ps.qual;
	outerPlan = outerPlanState(node);
	innerPlan = innerPlanState(node);
	econtext = node->js.ps.ps_ExprContext;

	/*
	 * Check to see if we're still projecting out tuples from a previous join
	 * tuple (because there is a function-returning-set in the projection
	 * expressions).  If so, try to project another one.
	 */
	if (node->js.ps.ps_TupFromTlist)
	{
		TupleTableSlot *result;
		ExprDoneCond isDone;

		result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);
		if (isDone == ExprMultipleResult)
			return result;
		/* Done with that source tuple... */
		node->js.ps.ps_TupFromTlist = false;
	}

	/*
	 * Reset per-tuple memory context to free any expression evaluation
	 * storage allocated in the previous tuple cycle.  Note this can't happen
	 * until we're done projecting out tuples from a join tuple.
	 */
	ResetExprContext(econtext);

	/*
	 * Ok, everything is setup for the join so now loop until we return a
	 * qualifying join tuple.
	 */
	ENL1_printf("entering main loop");
	elog(LOG, "------Let's rock baby!");
	for (;;)
	{
		/*
		 * If we don't have an outer tuple, get the next one and reset the
		 * inner scan.
		 */

		// ------mine starts here
		// fetch new outer "block"
		if (node->you_NeedNewOuterBlock)
		{
			int i;

			elog(LOG, "------ok, fetching new outer block");
			for (i = 0; i < node->you_BlockSize; i++)
			{
				node->you_Block[i] = ExecProcNode(outerPlan);
				if (TupIsNull(node->you_Block[i]))
				{
					elog(LOG, "------not enough outer tuple");
					break;
				}
			}
			node->you_CntOuter = i;
			if (i == 0)
			{
				elog(LOG, "no outer tuple, ending join");
				return NULL;
			}
			node->you_iOuter = 0;
			node->you_NeedNewOuterBlock = false;
			node->you_NeedNewInner = true;
			node->you_NeedNewOuter = false;
			memset(node->you_BlockMatched, false, sizeof(node->you_BlockMatched));
			// get all parameter? wrong here!
			for (i = 0; i < node->you_CntOuter; i++)
			{
				outerTupleSlot = ExecCopySlot(outerTupleSlot, node->you_Block[i]);
				foreach(lc, nl->nestParams)
				{
					NestLoopParam *nlp = (NestLoopParam *) lfirst(lc);
					int			paramno = nlp->paramno;
					ParamExecData *prm;
	
					prm = &(econtext->ecxt_param_exec_vals[paramno]);
					/* Param value should be an OUTER var */
					Assert(IsA(nlp->paramval, Var));
					Assert(nlp->paramval->varno == OUTER);
					Assert(nlp->paramval->varattno > 0);
					prm->value = slot_getattr(outerTupleSlot,
											  nlp->paramval->varattno,
											  &(prm->isnull));
					/* Flag parameter value as changed */
					innerPlan->chgParam = bms_add_member(innerPlan->chgParam,
														 paramno);
				}
			}
			// rescan inner plan here
			elog(LOG, "rescanning inner plan");
			ExecReScan(innerPlan);
		}
		
		// well, fetch new inner tuple
		if (node->you_NeedNewInner)
		{
			innerTupleSlot = ExecProcNode(innerPlan);
			node->you_NeedNewInner = false;
			if (TupIsNull(innerTupleSlot))
			{
				int i;
				elog(LOG, "no inner tuple, need new outer block");
				// TODO block join fro left and anti
				if (node->js.jointype == JOIN_LEFT || node->js.jointype == JOIN_ANTI)
					for (i = 0; i < node->you_CntOuter; i++)
					{
						if (node->you_BlockMatched[i]) continue;
						ResetExprContext(econtext);
						econtext->ecxt_outertuple = node->you_Block[i];
						econtext->ecxt_innertuple = node->nl_NullInnerTupleSlot;
						ENL1_printf("testing qualification for outer-join tuple");
	
						if (otherqual == NIL || ExecQual(otherqual, econtext, false))
						{
							/*
							 * qualification was satisfied so we project and return
							 * the slot containing the result tuple using
							 * ExecProject().
							 */
							TupleTableSlot *result;
							ExprDoneCond isDone;
	
							ENL1_printf("qualification succeeded, projecting tuple");
	
							result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);
	
							if (isDone != ExprEndResult)
							{
								node->js.ps.ps_TupFromTlist =
									(isDone == ExprMultipleResult);
								node->you_BlockMatched[i] = true;
								return result;
							}
						}
					}
				node->you_NeedNewOuterBlock = true;
				continue;
			}
			econtext->ecxt_innertuple = innerTupleSlot;
			node->you_iOuter = 0;
		}

		// now fetch new outer tuple from block
		if (node->you_iOuter >= node->you_CntOuter)
		{
			node->you_NeedNewInner = true;
			break;
		}
		outerTupleSlot = node->you_Block[node->you_iOuter++];
		Assert(!TupIsNull(outerTupleSlot));
		econtext->ecxt_outertuple = outerTupleSlot;
		ENL1_printf("testing qualification");

		if (ExecQual(joinqual, econtext, false))
		{		
			bool canreturn = false;

			TupleTableSlot *result;
			ExprDoneCond isDone;

			if (otherqual == NIL || ExecQual(otherqual, econtext, false))
			{
				/*
				 * qualification was satisfied so we project and return the
				 * slot containing the result tuple using ExecProject().
				 */

				ENL1_printf("qualification succeeded, projecting tuple");

				result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);

				if (isDone != ExprEndResult)
				{
					node->js.ps.ps_TupFromTlist = (isDone == ExprMultipleResult);
					canreturn = true;
				}
			}
			// TODO too slow for JOIN_ANTI
			if (node->js.jointype == JOIN_ANTI && node->you_BlockMatched[node->you_iOuter - 1]) continue;
			node->you_BlockMatched[node->you_iOuter - 1] = true;
			if (canreturn) return result;
		}
		
		// tuple fails qual
		ResetExprContext(econtext);
		ENL1_printf("qualification failed, looping");
		// ------mine ends here
	}
}

/* ----------------------------------------------------------------
 *		ExecInitNestLoop
 * ----------------------------------------------------------------
 */
NestLoopState *
ExecInitNestLoop(NestLoop *node, EState *estate, int eflags)
{
	NestLoopState *nlstate;

	/* check for unsupported flags */
	Assert(!(eflags & (EXEC_FLAG_BACKWARD | EXEC_FLAG_MARK)));

	NL1_printf("ExecInitNestLoop: %s\n",
			   "initializing node");

	/*
	 * create state structure
	 */
	nlstate = makeNode(NestLoopState);
	nlstate->js.ps.plan = (Plan *) node;
	nlstate->js.ps.state = estate;

	/*
	 * Miscellaneous initialization
	 *
	 * create expression context for node
	 */
	ExecAssignExprContext(estate, &nlstate->js.ps);

	/*
	 * initialize child expressions
	 */
	nlstate->js.ps.targetlist = (List *)
		ExecInitExpr((Expr *) node->join.plan.targetlist,
					 (PlanState *) nlstate);
	nlstate->js.ps.qual = (List *)
		ExecInitExpr((Expr *) node->join.plan.qual,
					 (PlanState *) nlstate);
	nlstate->js.jointype = node->join.jointype;
	nlstate->js.joinqual = (List *)
		ExecInitExpr((Expr *) node->join.joinqual,
					 (PlanState *) nlstate);

	/*
	 * initialize child nodes
	 *
	 * If we have no parameters to pass into the inner rel from the outer,
	 * tell the inner child that cheap rescans would be good.  If we do have
	 * such parameters, then there is no point in REWIND support at all in the
	 * inner child, because it will always be rescanned with fresh parameter
	 * values.
	 */
	outerPlanState(nlstate) = ExecInitNode(outerPlan(node), estate, eflags);
	if (node->nestParams == NIL)
		eflags |= EXEC_FLAG_REWIND;
	else
		eflags &= ~EXEC_FLAG_REWIND;
	innerPlanState(nlstate) = ExecInitNode(innerPlan(node), estate, eflags);

	/*
	 * tuple table initialization
	 */
	ExecInitResultTupleSlot(estate, &nlstate->js.ps);

	switch (node->join.jointype)
	{
		case JOIN_INNER:
		case JOIN_SEMI:
			break;
		case JOIN_LEFT:
		case JOIN_ANTI:
			nlstate->nl_NullInnerTupleSlot =
				ExecInitNullTupleSlot(estate,
								 ExecGetResultType(innerPlanState(nlstate)));
			break;
		default:
			elog(ERROR, "unrecognized join type: %d",
				 (int) node->join.jointype);
	}

	/*
	 * initialize tuple type and projection info
	 */
	ExecAssignResultTypeFromTL(&nlstate->js.ps);
	ExecAssignProjectionInfo(&nlstate->js.ps, NULL);

	/*
	 * finally, wipe the current outer tuple clean.
	 */
	nlstate->js.ps.ps_TupFromTlist = false;
	nlstate->nl_NeedNewOuter = true;
	nlstate->nl_MatchedOuter = false;
	
	// ------mine starts here
	int i;

	nlstate->you_NeedNewOuterBlock = true;
	nlstate->you_NeedNewInner = false;
	nlstate->you_NeedNewOuter = false;
	nlstate->you_BlockSize = 8;
	nlstate->you_CntOuter = 0;
	nlstate->you_iOuter = 0;
	// construct block
	nlstate->you_Block = (TupleTableSlot**) malloc(sizeof(TupleTableSlot*) * (nlstate->you_BlockSize + 10));
	for (i = 0; i < nlstate->you_BlockSize; i++)
		nlstate->you_Block[i] = 
			ExecInitNullTupleSlot(estate,
				ExecGetResultType(outerPlanState(nlstate)));
	nlstate->you_BlockMatched = (bool*) malloc(sizeof(bool) * (nlstate->you_BlockSize + 10));
	memset(nlstate->you_BlockMatched, false, sizeof(nlstate->you_BlockMatched));
	// ------mine ends here

	NL1_printf("ExecInitNestLoop: %s\n",
			   "node initialized");
	return nlstate;
}

/* ----------------------------------------------------------------
 *		ExecEndNestLoop
 *
 *		closes down scans and frees allocated storage
 * ----------------------------------------------------------------
 */
void
ExecEndNestLoop(NestLoopState *node)
{
	NL1_printf("ExecEndNestLoop: %s\n",
			   "ending node processing");

	/*
	 * Free the exprcontext
	 */
	ExecFreeExprContext(&node->js.ps);

	// ------mine starts here
	free(node->you_Block);
	free(node->you_BlockMatched);
	// ------mine ends here

	/*
	 * clean out the tuple table
	 */
	ExecClearTuple(node->js.ps.ps_ResultTupleSlot);

	/*
	 * close down subplans
	 */
	ExecEndNode(outerPlanState(node));
	ExecEndNode(innerPlanState(node));

	NL1_printf("ExecEndNestLoop: %s\n",
			   "node processing ended");
}

/* ----------------------------------------------------------------
 *		ExecReScanNestLoop
 * ----------------------------------------------------------------
 */
void
ExecReScanNestLoop(NestLoopState *node)
{
	PlanState  *outerPlan = outerPlanState(node);

	/*
	 * If outerPlan->chgParam is not null then plan will be automatically
	 * re-scanned by first ExecProcNode.
	 */
	if (outerPlan->chgParam == NULL)
		ExecReScan(outerPlan);

	/*
	 * innerPlan is re-scanned for each new outer tuple and MUST NOT be
	 * re-scanned from here or you'll get troubles from inner index scans when
	 * outer Vars are used as run-time keys...
	 */

	node->js.ps.ps_TupFromTlist = false;
	node->nl_NeedNewOuter = true;
	node->nl_MatchedOuter = false;

	// ------mine starts here
	node->you_NeedNewOuterBlock = true;
	node->you_NeedNewInner = false;
	node->you_NeedNewOuter = false;
	// ------mine ends here
}
