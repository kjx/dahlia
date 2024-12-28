// objects are "contextually OK"




///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///COK / CallOK  (not yet in the right order)
///Probablu should go off to another file?

lemma COKAMFO(oo : Owner, context : set<Object>)
  decreases oo
  requires CallOK(oo, context)
  requires CallOK(context)
  ensures  CallOK(flattenAMFOs(oo), context)
{
  reveal COK();
  reveal CallOK();
}


lemma COKowner(a : Object, context : set<Object>)
  decreases a.AMFO
  requires COK(a, context)
  requires CallOK(context)

  ensures  CallOK(a.owner, context)
  ensures  AllTheseOwnersAreFlatOK(a.AMFO - {a})
  ensures  AllTheseOwnersAreFlatOK(a.allExternalOwners())
  ensures  a.OwnersValid()
{
  reveal COK();
  reveal CallOK();
}




lemma CallOKAMFO(aa : Owner, context : set<Object>)
  requires CallOK(aa, context)
  requires CallOK(context)
  ensures  forall a <- aa :: CallOK(a.AMFO, context)
  ensures  forall a <- aa :: a.AMFO <= context
{
  reveal COK();
  reveal CallOK();
}


lemma COKgetsDeclaredFields(a : Object, context : set<Object>)
  requires COK(a, context)
  ensures a.AllFieldsAreDeclared()
{
   reveal COK();
  //  assert COK(a, context);
  //  assert a.Valid();
  //  assert a.AllFieldsAreDeclared();
}


lemma COKWiderContext2(a : Object, less : set<Object>, more : set<Object>)
//given COK(a,less) get COK(a, more)
  requires a in less
  requires COK(a,less)
  requires less <= more
  ensures COK(a,more)
{
  reveal COK();
}


lemma COKWiderContext(a : Object, context : set<Object>, extra : set<Object>)
  requires a in context
  requires COK(a,context)
  ensures COK(a,context + extra)
{
  reveal COK();
}

lemma CallOKWiderContext(aa: set<Object>, context : set<Object>, extra : set<Object>)
  requires aa <= context
  requires CallOK(aa,context)
  ensures CallOK(aa,context + extra)
{
  reveal CallOK();
  forall a <- aa { COKWiderContext(a,context,extra); }
}

lemma CallOKWiderContext2(aa: set<Object>, less : set<Object>, more : set<Object>)
  requires aa <= less <= more
  requires CallOK(aa,less)
  ensures CallOK(aa,more)
{
  reveal CallOK();
  forall a <- aa { COKWiderContext2(a,less,more); }
}



lemma CallOKWiderFocus(aa: set<Object>, bb : set<Object>, context : set<Object>)
  requires aa <= context
  requires bb <= context
  requires CallOK(aa,context)
  requires CallOK(bb,context)
  ensures  CallOK(aa+bb,context)
{
  reveal CallOK();
  assert forall a <- (aa     ) :: COK(a,context);
  assert forall a <- (     bb) :: COK(a,context);
  assert forall a <- (aa + bb) :: COK(a,context);
}


lemma CallOKWiderFocus2(less: set<Object>, more : set<Object>, context : set<Object>)
  requires less <= more <= context
  requires CallOK(less,context)
  requires CallOK((more - less), context)
  ensures  CallOK(more,context)
{
  reveal CallOK();
  assert forall a <- (less)        :: COK(a,context);
  assert forall a <- (more - less) :: COK(a,context);
  assert forall a <- (more)        :: COK(a,context);
}



///IF owners OK were also bounded by a (sub)heap, then
///the reads clauses could just look over that whole subheap...
///that way lies... seplogic?
opaque predicate COK(a : Object, context : set<Object>) : (r : bool)
//NOTE Pulled fields from COK - owners etc in context
//  reads context`fields, context`fieldModes
  reads a`fields, a`fieldModes

  // reads (set x <- a.extra, xa <- x.AMFO :: xa)`fields
  // reads (set x <- a.extra, xa <- x.AMFO :: xa)`fieldModes
  // reads  a.extra`fields, a.extra`fieldModes

  // reads (set o1 <- context, o2 <- o1.ValidReadSet() :: o2)`fields
  // reads (set o1 <- context, o2 <- o1.ValidReadSet() :: o2)`fieldModes
  ensures r ==> (a in context)
 {
//extraOK   && a.extra == {}  //extra not yet cloned

    && (a in context)
    //&& (a.AMFO <= context)
    //&& (a.AMFB <= context) //sgould be derivable, AMFB <= AMFO
    && (a.AMFB <= a.AMFO <= context)
    && (forall oo <- a.AMFO :: oo.Ready())
  //  && (a.TRUMP()||(a.Ready() && a.Valid()))
    && (a.Ready())
    && (a.Valid())
    && (a.AllOutgoingReferencesAreOwnership(context))
//    && (a.AllOutgoingReferencesWithinThisHeap(context))
    && (a.AllOwnersAreWithinThisHeap(context))

    && AllTheseOwnersAreFlatOK(a.AMFO - {a})   //point here is we don't want a loop  in the definitoin of the COK predicate I think()
//KJX redo to be a.AllExternalOwners() (or AMXO?)
//now surfaced by COKowner :-)
//should it be within the context?? (or owners are within this heap doe sthat!)
 }

method COKat(a : Object, n : string, context : set<Object>) returns ( r : Object )
  requires COK(a,context)
  requires CallOK(context)
  requires n in a.fields
  requires a.Ready()  //comes from COK?
  requires a.AllOutgoingReferencesWithinThisHeap(context)
  requires forall x <- context :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(context)

  ensures r == a.fields[n]
  ensures COK(r,context)
  modifies {}
{
  reveal COK(); reveal CallOK();
  r := a.fields[n];
  assert COK(a,context);

  assert (a.AllOutgoingReferencesAreOwnership(context));
  assert (a.AllOutgoingReferencesWithinThisHeap(context));
  assert (a.AllOwnersAreWithinThisHeap(context));

  assert (r in context);
  assert CallOK(context);
  assert forall x <- context :: x.AllOutgoingReferencesAreOwnership(context);
  assert forall x <- context :: x.AllOutgoingReferencesWithinThisHeap(context);
  assert forall x <- context :: x.AllOwnersAreWithinThisHeap(context);
  assert (r.AMFO <= context);
  assert (forall oo <- r.AMFO :: oo.Ready());
  assert (r.Ready() && r.Valid());
  assert (r.AllOutgoingReferencesAreOwnership(context));
  assert (r.AllOutgoingReferencesWithinThisHeap(context));
  assert (r.AllOwnersAreWithinThisHeap(context));


  assert  COK(r,context);
}

opaque predicate CallOK(aa :set<Object>, context : set<Object> := aa)
  reads aa`fields, aa`fieldModes
//  reads context`fields, context`fieldModes
  // reads (set o1 <- context, o2 <- o1.ValidReadSet() :: o2)`fields
  // reads (set o1 <- context, o2 <- o1.ValidReadSet() :: o2)`fieldModes
{
  forall a <- aa :: COK(a,context)
}



lemma CallOKtoSubset(aa :set<Object>, context : set<Object> := aa)
  requires CallOK(aa, context)
  ensures  aa <= context
  {
    reveal CallOK();
    assert forall a <- aa :: COK(a,context);
    reveal COK();
    assert forall a <- aa :: a in context;
    assert aa <= context;
  }

lemma CallOKNarrowFocus(nn : set<Object>, aa : set<Object>, context : set<Object> := aa)
  requires CallOK(aa, context)
  requires nn <= aa
  ensures  CallOK(nn, context)
  {
    reveal CallOK();
    assert forall a <- aa :: COK(a,context);
    reveal COK();
    assert forall a <- nn :: COK(a,context);
  }


lemma COKNarrowContext(a : Object, less : set<Object>, more : set<Object>)
  requires less <= more
  requires COK(a, more)
  requires a.AMFO <= less
  requires a.Ready()
//  requires a.AllOutgoingReferencesWithinThisHeap(less)
  ensures  COK(a, less)
{
  reveal COK();
}

lemma COKfromCallOK(a : Object, focus : set<Object>, context : set<Object>  := focus)
  requires CallOK(focus, context)
  requires a in focus
  ensures COK(a, context)
  {
    reveal CallOK();
  }


lemma CallOKfromCOK(a : Object, context : set<Object>)
  requires COK(a, context)
  ensures  CallOK({a}, context)
  {
    reveal CallOK();
  }

lemma RVfromCOK(a : Object, context : set<Object>)
  requires COK(a, context)
  ensures a.Ready()
  ensures a.Valid()
  ensures a.AMFO <= context
  ensures (forall oo <- a.AMFO :: oo.Ready())
  {
    reveal COK();
  }

lemma RVfromCallOK(aa : set<Object>, context : set<Object>)
  requires CallOK(aa, context)
  ensures  (forall a <- aa :: a.Ready())
  ensures  (forall a <- aa :: a.Valid())
  ensures  (forall a <- aa :: a.AMFO <= context)
  ensures  (forall a <- aa, oo <- a.AMFO :: oo.Ready())
  {
    reveal COK(), CallOK();
  }
