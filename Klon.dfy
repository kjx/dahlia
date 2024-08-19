 
type Mapping = map<Object,Object>

 
///shoujld thsi be m.KEys or m.ks... 
predicate OrigMapOK(m : Mapping)
{
  && (forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys)
  && (forall x <- m.Keys :: x.region.Heap? == m[x].region.Heap?)
  && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO)
  && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in m.Keys)
  && (forall x <- m.Keys |  x.region.Heap? :: m[x.region.owner] == m[x].region.owner )
  && (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO)
//  && forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x))x
}
predicate MapOK(m : Mapping)
{
  && (forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys)
  && (forall x <- m.Keys :: x.region.Heap? == m[x].region.Heap?)
  && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO)
  && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in m.Keys)
  && (forall x <- m.Keys |  x.region.Heap? :: m[x.region.owner] == m[x].region.owner )
  && (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO)
//  && forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x))

  && (forall x <- m.Keys |  x.region.Heap? :: x.extra <= x.AMFO)
  && (forall x <- m.Keys |  x.region.Heap? :: x.extra <= m.Keys)
  && (forall x <- m.Keys, xo <- x.extra :: xo in m.Keys)
  && (forall x <- m.Keys, xo <- x.extra :: m[xo] in m[x].extra)  
}


function MapKV(m : Mapping,   x : Object,  v : Object) : (r : Mapping) 
  requires MapOK(m)
  ensures  MapOK(r)
requires  //the below should be a predicate (from MapKV)
  && x !in m.Keys
  //&& COK(x,m.Keys)
  && x.Ready() && v.Ready()
  && (forall oo <- (x.AMFO - {x}) :: oo in m.Keys)
  && (x.region.Heap? == v.region.Heap?)
  && (x.region.Heap? ==> x.region.owner in x.AMFO)
  && (x.region.Heap? ==> x.region.owner in m.Keys)
  && (forall oo <- (x.AMFO - {x}) :: oo in m.Keys &&  m[oo] in v.AMFO)
  && (x.region.Heap? ==> x.region.owner in (x.AMFO - {x}))
  && (x.region.Heap? ==> m[x.region.owner] == v.region.owner)
  && (x.region.Heap? ==> x.extra <= x.AMFO)
  && (forall xo <- x.extra :: xo in m.Keys)
  && (forall xo <- x.extra :: m[xo] in v.extra)  
{
  reveal COK();
  var r := m[x:=v];
//  assert COK(x,m.Keys);
  assert MapOK(m);
  assert r.Keys == m.Keys + {x};

  assert m.Keys <= r.Keys;
  assert forall k <- m.Keys :: k in r.Keys;
  assert forall k <- r.Keys :: (k in m.Keys) || (k == x);
  assert forall k <- r.Keys :: 
    if (k in m.Keys) then r[k] == m[k] else r[k] == v;
// 
//   assert (forall x <- r.Keys, oo <- x.AMFO :: r[oo] in r[x].AMFO) by {
//             assert (forall oo <- x.AMFO :: r[oo] in r[x].AMFO);
//             assert (forall x <- m.Keys, oo <- x.AMFO :: r[oo] in r[x].AMFO);
//             assert r.Keys == m.Keys + {x};
//             assert (forall x <- r.Keys, oo <- x.AMFO :: r[oo] in r[x].AMFO);  
//             } 
//   assert (forall x <- r.Keys | x.region.Heap? :: r[x.region.owner] == r[x].region.owner) by {
//             assert (forall x <- m.Keys | x.region.Heap? :: m[x.region.owner] == r[x].region.owner);
//             assert (forall x <- m.Keys |  x.region.Heap? :: m[x.region.owner] == r[x].region.owner);
//             assert r.Keys == m.Keys + {x};
//             assert (forall x <- r.Keys | x.region.Heap? :: r[x.region.owner] == r[x].region.owner);          
//             }

  assert (forall x <- r.Keys :: x.region.Heap? == r[x].region.Heap?) by {
      assert (forall x <- m.Keys :: x.region.Heap? == r[x].region.Heap?); 
      assert r.Keys == m.Keys + {x};
      assert (forall x <- r.Keys :: x.region.Heap? == r[x].region.Heap?); 
  }

   assert (&& (forall x <- m.Keys, xo <- x.extra :: xo in m.Keys)
           && (forall x <- r.Keys, xo <- x.extra :: r[xo] in r[x].extra)) by {
      assert (forall x <- m.Keys, xo <- x.extra :: m[xo] in m[x].extra);
      assert forall k <- r.Keys :: 
        if (k in m.Keys) then r[k] == m[k] else r[k] == v;      
      assert (forall x <- m.Keys, xo <- x.extra :: r[xo] in m[x].extra);
      assert r.Keys == m.Keys + {x};
      assert x in r.Keys;
      assert (forall xo <- x.extra :: m[xo] in v.extra);
      assert (forall x <- r.Keys, xo <- x.extra :: r[xo] in r[x].extra);
  }  



  assert (forall x <- r.Keys |  x.region.Heap? :: r[x.region.owner] == r[x].region.owner ) 
    by {
      assert MapOK(m);
      assert (forall x <- m.Keys |  x.region.Heap? ::  m[x.region.owner] == m[x].region.owner );
      assert forall k <- r.Keys :: 
        if (k in m.Keys) then r[k] == m[k] else r[k] == v;
      assert (forall x <- m.Keys |  x.region.Heap? ::  r[x.region.owner] == r[x].region.owner );
      assert x.region.Heap? ==>  (r[x.region.owner] == r[x].region.owner);
      assert (forall x <- r.Keys |  x.region.Heap? :: r[x.region.owner] == r[x].region.owner );
    } 

  assert (forall x <- r.Keys, oo <- x.AMFO :: r[oo] in r[x].AMFO)
    by {
      assert MapOK(m);
      assert (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO);
      assert forall k <- r.Keys :: 
        if (k in m.Keys) then r[k] == m[k] else r[k] == v;
      assert (forall x <- m.Keys, oo <- x.AMFO :: r[oo] in r[x].AMFO);
      assert (forall oo <- x.AMFO - {x} :: r[oo] in v.AMFO);
      assert r[x] == v;
      assert (x in x.AMFO) && (v in v.AMFO) && (r[x] in r[x].AMFO);
      assert (forall x <- r.Keys, oo <- x.AMFO :: r[oo] in r[x].AMFO);
    } 




  assert MapOK(r);
  r
}


datatype Map = Map(
    m : Mapping,  //m : Mapping 
    ks : set<Object>, //ks - set, keys of the mapping   (must be m.Keys, subset of oHeap)
    vs : set<Object>, //vs - set, values or the mapping (must be m.Values, subset of oHeap + ns)
    o : Object,  //o - Owner within which the clone is being performaed, in oHeap
    oHeap : set<Object>,  //oHeap - original (sub)heap contianing the object being cloned and all owners and parts 
    ns : set<Object>) //ns - new objects  (must be !! oHeap,   vs <= oHeap + ns 
   {
   // general rule: where possible, work with ks and vs rther than m.Keys & m.Values...
   // that's the point of setting this up, right?



   predicate from(other : Map) 
   // should this be unique or not?
   // m.from(other) assuming other.MapOK, then I',m Map(OK) and a a "strict but improper extension"
   // strict - thijngs like oHeap can't change
   // improper - could be exactly the same as other 
   //
   // if most things are OK,  given xown, xm := foo(own, m);
   // then we should have xm.from(m);  I THINK??
   //
  /// what's really annoy6ing is: should I keep track of the first from?
  // cos usually that's what I need to prove.
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    reads other.oHeap`fields, other.oHeap`fieldModes
    reads other.ns`fields, other.ns`fieldModes

    requires calid()
    requires other.calid()
    {  
       reveal calid(), calidObjects(), calidOK(), calidMap(), calidSheep();
       && calid()         //should these be requirements?  
       && other.calid()   //currently YES because the underlyign thing will require calid and reutnr calid
       && mapGEQ(m, other.m)
       && ks    >= other.ks
       && vs    >= other.vs
       && o     == other.o
       && oHeap == other.oHeap
       && ns    >= other.ns   
    }

    opaque function at(k : Object) : (v : Object)
      //return value corresponding to key k
      //k must be in the map
      reads oHeap`fields, oHeap`fieldModes
      reads ns`fields, ns`fieldModes      
      requires calid()
      requires k in ks
      //requires reveal calid(); reveal calidObjects();  ks == m.Keys
      //requires k in m.Keys 
      ensures  k in ks
      ensures  k in m.Keys //to guard the next one
      ensures  v == m[k]
        {  reveal calid(); reveal calidObjects(); 
           assert k in m.Keys;
           m[k] }

    opaque predicate  {:onleee} got(k : Object) : (g : bool)
      //is k in the map?
      reads oHeap`fields, oHeap`fieldModes
      reads ns`fields, ns`fieldModes
      requires calid()
      ensures  g == (k in ks)
      ensures  g == (k in m.Keys)  //DO I WANT THIS?
      { 
        reveal calid();
        assert calid();
        reveal calidObjects();
        assert calidObjects();
        k in ks
      }


    opaque predicate gotV(v : Object) : (g : bool)
      //is v a value in the map?
      reads oHeap`fields, oHeap`fieldModes
      reads ns`fields, ns`fieldModes
      requires calid()
      ensures  g == (v in vs)
      ensures  g == (v in m.Values)  //DO I WANT THIS?
      { 
        reveal calid();
        assert calid();
        reveal calidObjects();
        assert calidObjects();
        v in vs 
      }


    opaque function {:isolate_assertions} putInside(k : Object, v : Object) : (r : Map)
      //put k -> v into map, k inside o
      reads oHeap`fields, oHeap`fieldModes
      reads ns`fields, ns`fieldModes,  v`fields, v`fieldModes     
      requires calid()
      requires k  in oHeap
      requires k !in ks
      requires k !in m.Keys
      requires v !in oHeap
      requires v !in ns
      requires v !in vs
      requires v !in m.Values
      requires COK(k, oHeap)
      requires COK(v, oHeap+ns+{v})
      requires ks <= oHeap
      requires k.owners() <= ks  //need to update - all my owners EXCEPT ME!
      requires k.owners() <= m.Keys 
      requires v.owners() <= oHeap+ns //need to hae proceessed all owners first
      // requires v in (oHeap + ns) // should be a SEPERATIJG COJUNCTION (Below)
      // requires ((v in oHeap) != (v in ns))  //NOPE for now put it in ns
      requires k.region.Heap? == v.region.Heap?
      requires k.region.Heap? ==> v.region.Heap? && (k.region.owner in m.Keys) && (m[k.region.owner] == v.region.owner)
      requires forall ko <- k.owners() :: ko in m.Keys
      requires forall ko <- k.owners() :: m[ko] in v.AMFO

      requires forall kx <- k.extra :: kx in m.Keys
      requires forall kx <- k.extra :: m[kx] in v.extra
//      requires k.region.Heap? ==> (k.region.owner in m && m[k.region.owner] == v.region.owner)
//      requires reveal calid(); (calid() && k.region.Heap?) ==> (got(k.region.owner) && (at(k.region.owner) == v.region.owner))
      //requires fresh(v)
      requires inside(k, o)
      requires v.fieldModes == k.fieldModes

      ensures  r == Map(m[k:=v], ks+{k}, vs+{v}, o, oHeap, ns+{v})
      ensures  r.m.Keys == r.ks
      ensures  r.m.Values == r.vs
      ensures  v in r.ns
      ensures  k in r.ks && r.m[k] == v
      ensures  COK(v, r.oHeap+r.ns)
      ensures  k in r.m.Keys
      ensures  v in r.m.Values
      ensures  r.m == m[k:=v]
      ensures  r.m == MappingPlusOneKeyValue(this.m,k,v)
      ensures  mapLEQ(m, r.m)
      ensures  r.calid()
      ensures  r.from(this)
      {   
        reveal calid(); assert calid();
        var rv := Map(m[k:=v], ks+{k}, vs+{v}, o, oHeap, ns+{v});


        assert oXn: oHeap !! ns by { assert calid(); assert calidObjects(); reveal calidObjects();}

          assert COK(v, rv.oHeap+rv.ns) by {
            assert COK(v, oHeap+ns+{v});  // from reqs
            assert rv.oHeap      == oHeap;
            assert rv.ns         == ns+{v};
            assert rv.oHeap+rv.ns == oHeap+ns+{v};
            assert COK(v, rv.oHeap+rv.ns);
          }

          assert rv.calidObjects() by {
            reveal rv.calidObjects();

            assert rv.ks == rv.m.Keys;
            assert rv.vs == rv.m.Values;
            assert rv.o in rv.oHeap;
            assert rv.ks <= rv.oHeap;
            assert    ns !!    oHeap by { reveal oXn; } 
            assert rv.ns !! rv.oHeap by { assert rv.oHeap == oHeap; assert rv.ns == ns+{v}; }
            assert rv.vs <= rv.ns + oHeap;

            assert rv.calidObjects(); 
          }

          assert v !in vs; // from reqs
          assert vs == m.Values by { 
            assert calid();
            reveal calid();
            assert calidObjects();
            reveal calidObjects();
            assert vs == m.Values;
                   }
          assert v !in m.Values;

          assert rv.calidOK() by {
            reveal rv.calidOK();
            reveal rv.calidObjects();
            assert COK(rv.o, rv.oHeap);
            assert CallOK(rv.oHeap);
            CallOKfromCOK(k, oHeap);
            assert CallOK(ks, oHeap);
            CallOKtoSubset(ks, oHeap);
            CallOKWiderFocus(ks, {k}, oHeap);
            assert CallOK(rv.ks, rv.oHeap);
            assert oHeap+ns+{v} == rv.oHeap+rv.ns;
            assert COK(v, rv.oHeap+rv.ns);
            // CallOKWiderContext({v}, rv.oHeap, rv.ns);    //unneeded?
            // CallOKtoSubset(rv.vs, rv.oHeap+rv.ns);       //unneeded?
            assert rv.vs <= rv.ns + oHeap;
            assert CallOK(vs, oHeap+ns);
            CallOKWiderContext(vs, oHeap+ns, {v});
            assert COK(v,oHeap+ns+{v}); //reqs
            CallOKfromCOK(v, oHeap+ns+{v});   //could subsume within COK?> (or not0)
            CallOKWiderFocus(vs, {v}, oHeap+ns+{v});  //version just adding one?
            assert vs+{v} == rv.vs;
            assert CallOK(rv.vs, rv.oHeap+rv.ns);
            assert ns+{v} == rv.ns;
            CallOKWiderContext(ns,oHeap+ns,{v});  //is it worth cobinging these also
            CallOKWiderFocus(ns,{v},oHeap+ns+{v});
            assert CallOK(rv.ns, rv.oHeap+rv.ns);
            reveal rv.calidOK(); assert rv.calidOK();
          }


          // reveal rv.calidMap();
          // assert rv.calidMap() by {
            reveal rv.calidMap();
            assert MapOK(rv.m) by {
                assert MapOK(m);
                assert COK(k, oHeap);
                reveal COK();
                assert rv.ks == ks + {k};          
                assert rv.m.Keys == m.Keys + {k};

                reveal rv.calidObjects();
                assert rv.calidObjects();
                reveal calidObjects();
                assert calidObjects();
                reveal calidMap();
                assert calidMap();

                assert rv.m.Keys == rv.ks;
                assert k.owners() <= ks;

                assert forall x <- m.Keys :: x.AMFO <= ks by { 
                  assert forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys;
                }  
                assert k.owners() <= ks;
              //  assert forall x <- m.Keys+{k} :: x.owner() <= ks;
                assert forall x <- m.Keys+{k} :: x.AMFO <= ks+{k};
                assert (ks+{k}) == m.Keys+{k} == rv.ks == rv.m.Keys;
                assert forall x <- rv.m.Keys :: x.AMFO <= rv.m.Keys;
                assert forall x <- rv.m.Keys, oo <- x.AMFO :: oo in rv.m.Keys;

                assert (forall x <- rv.m.Keys :: x.region.Heap? == rv.m[x].region.Heap?);
                assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO);
                assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.region.owner in rv.m.Keys);
                assert (forall x <- rv.m.Keys |  x.region.Heap? :: rv.m[x.region.owner] == rv.m[x].region.owner );

              assert (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO);
              assert (forall x <- m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
              assert rv.m[k] == v;
              assert ks == m.Keys;
              assert (k.owners() <= ks);
              assert (k.AMFO - {k}) <= ks;
              assert (forall oo <- (k.AMFO - {k}):: oo in m.Keys); 
              assert (forall oo <- (k.AMFO - {k}):: m[oo] in v.AMFO); 
              assert (forall oo <- (k.AMFO - {k}):: rv.m[oo] in rv.m[k].AMFO); 

              assert (forall x <- m.Keys, xo <- x.extra :: xo in m.Keys);
              assert (forall x <- m.Keys, xo <- x.extra :: m[xo] in m[x].extra);
              assert (forall x <- m.Keys, xo <- x.extra :: xo in rv.m.Keys);
              assert (forall x <- m.Keys, xo <- x.extra :: rv.m[xo] in rv.m[x].extra);



              assert (forall xo <- k.extra :: xo in rv.m.Keys); 
              assert (forall xo <- k.extra :: rv.m[xo] in rv.m[k].extra);

                assert rv.m.Keys == m.Keys + {k};

                assert (forall x <- rv.m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
                assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.extra <= x.AMFO);
                assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.extra <= rv.m.Keys);
                assert (forall x <- rv.m.Keys, xo <- x.extra :: xo in rv.m.Keys);
                assert (forall x <- rv.m.Keys, xo <- x.extra :: rv.m[xo] in rv.m[x].extra);
            }  //MAapOK


        
            reveal rv.calidObjects();
            assert ks == m.Keys;
            assert rv.ks == rv.m.Keys;
            assert (forall x <- rv.ks :: (not(inside(x,rv.o)) ==> (rv.m[x] == x)));
            assert (forall x <- rv.m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
            assert (forall x <- ks, oo <- x.AMFO :: m[oo] in m[x].AMFO);
            reveal rv.calidMap();
            assert rv.calidMap();

                reveal rv.calidSheep();
                reveal rv.calidObjects();
                assert ks == m.Keys;
                assert rv.ks == rv.m.Keys;
            assert inside(k, o);
            reveal calidMap();
            assert calidMap();
            reveal calidSheep();

            
            assert forall x <- ks :: AreWeNotMen(x, this);
            assert rv.ks == rv.m.Keys == (ks+{k});

            assert forall x <- ks :: x.fieldModes == m[x].fieldModes;
            assert k.fieldModes == v.fieldModes;
            assert forall x <- rv.ks :: x.fieldModes == rv.m[x].fieldModes;

            assert calidSheep();
            reveal rv.calidSheep();
            //reveal UniqueMapEntry();

            assert ks == m.Keys;

                reveal AreWeNotMen();  
                reveal UniqueMapEntry();
            assert forall x <- ks  :: AreWeNotMen(x, this); 
            assert forall x <- {k} :: AreWeNotMen(x, rv);
            assert forall x <- rv.m.Keys :: AreWeNotMen(x, rv);

            assert rv.calidSheep();
            reveal rv.calid(); assert rv.calid();

            rv
}
      



    opaque function {:isolate_assertions} {:timeLimit 40} putOutside(k : Object) : (r : Map)
      //put k -> k into map, k oustide o
      reads oHeap`fields, oHeap`fieldModes
      reads ns`fields, ns`fieldModes
      requires calid()
      requires k !in ks
      requires k !in vs
      requires k !in m.Keys
      requires k !in m.Values
      requires k in oHeap
      requires COK(k, oHeap)
      requires k.owners() <= ks
      requires not(inside(k, o))

requires
  && k !in m.Keys
  && COK(k,oHeap)
  && k.Ready()
  && k.AllOwnersAreWithinThisHeap(ks)
  && (forall oo <- k.AMFO - {k}:: oo in m.Keys)
  //  && (k.region.Heap? ==> m[k].region.Heap?)  WHATR THE FUCK k at in the map!
  && (k.region.Heap? ==> k.region.owner in k.AMFO)
  && (k.region.Heap? ==> k.region.owner in m.Keys)
  // && (k.region.Heap? ==> m[k.region.owner] == m[k].region.owner )
  //  && (forall oo <- k.AMFO :: m[oo] in m[k].AMFO)
  && (k.region.Heap? ==> k.extra <= k.AMFO)
  && (forall xo <- k.extra :: xo in m.Keys)
  // && (forall xo <- k.extra :: m[xo] in m[k].extra) 




      requires forall kx <- k.extra :: kx in m.Keys
      requires forall kx <- k.extra :: m[kx] == kx

      ensures r == Map(m[k:=k], ks+{k}, vs+{k}, o, oHeap, ns)
      ensures k in r.ks && r.m[k] == k
      ensures k in r.m.Keys
      ensures k in r.m.Values
      ensures MapOK(r.m)
      ensures weirdo() && (r.m == MapKV(this.m,k,k))
      ensures mapLEQ(m, r.m)
      ensures r.calid()
      ensures r.from(this)
{

assert  //the below should be a predicate (from MapKV)
  && k !in m.Keys
  //&& COK(k,m.Keys)
  && (forall oo <- k.AMFO - {k} :: oo in m.Keys)
  //&& (k.region.Heap? ==> m[k].region.Heap?)
  && (k.region.Heap? ==> k.region.owner in k.AMFO)
  && (k.region.Heap? ==> k.region.owner in m.Keys)
  //&& (k.region.Heap? ==> m[k.region.owner] == m[k].region.owner )
  //&& (forall oo <- k.AMFO :: m[oo] in m[k].AMFO)
  && (k.region.Heap? ==> k.extra <= k.AMFO)
  && (forall xo <- k.extra :: xo in m.Keys)
  //&& (forall xo <- k.extra :: m[xo] in m[k].extra) 
  ;

  reveal calid();
  assert calid();
  reveal calidObjects();
  assert calidObjects();
  reveal calidOK();
  assert calidOK();
  
  assert ks == m.Keys;
  assert calidMap();
  reveal calidMap();
  assert calidSheep();
  reveal calidSheep();

  assert MapOK(m);
  assert CallOK(oHeap);

  var numap := MapKV(m,k,k);
  assert MapOK(numap);

  var rv := Map(numap, ks+{k}, vs+{k}, o, oHeap, ns);

  assert rv == Map(m[k:=k], ks+{k}, vs+{k}, o, oHeap, ns);
  assert k in rv.ks && rv.m[k] == k;
  assert k in rv.m.Keys;
  assert k in rv.m.Values;
  assert MapOK(rv.m);
  assert weirdo() && (rv.m == MapKV(this.m,k,k));
  assert mapLEQ(m, rv.m);
  assert rv.calidObjects();
  

  assert rv.calidOK() by {
      assert (rv.o in rv.oHeap);
      assert (rv.ks <= rv.oHeap);
      assert (rv.vs <= rv.oHeap+ns);
      assert COK(rv.o, rv.oHeap) by { assert COK(o,oHeap);  assert rv.oHeap == oHeap; assert rv.o == o; }
      assert CallOK(rv.oHeap)    by { assert CallOK(oHeap); assert rv.oHeap == oHeap; }
      assert CallOK(rv.ks, rv.oHeap) by { assert CallOK(ks, oHeap); 
                                          assert COK(k,oHeap); 
                                          CallOKfromCOK(k,oHeap);
                                          CallOKWiderFocus(ks,{k},oHeap);
                                          assert rv.oHeap == oHeap; 
                                          assert rv.ks == ks+{k}; }
      assert CallOK(rv.vs, rv.oHeap+rv.ns) by { assert CallOK(vs, oHeap+ns);
                                                assert COK(k,oHeap);
                                                CallOKfromCOK(k,oHeap);
                                                CallOKWiderContext({k},oHeap,ns);
                                                CallOKWiderFocus(vs,{k},oHeap+ns); 
                                                assert rv.oHeap+rv.ns == oHeap+ns;
                                                assert rv.vs == vs+{k}; }
      assert CallOK(rv.ns, rv.oHeap+rv.ns) by { assert CallOK(ns, oHeap+ns);
                                                assert rv.oHeap == oHeap;
                                                assert rv.ns == ns; } 
      assert rv.calidOK();
  } 

  reveal rv.calidMap();
  assert rv.calidMap();
  reveal calidObjects(); assert calidObjects();
  reveal calidOK(); assert calidOK(); 
  reveal rv.calidSheep();
  assert rv.ks == rv.m.Keys;
  reveal AreWeNotMen(); 
  assert (forall x <- rv.ks :: AreWeNotMen(x, rv));
  assert (forall x <- rv.ks :: x.fieldModes == rv.m[x].fieldModes);
  assert rv.calidSheep();
  reveal rv.calid();
  assert rv.calid();
  assert rv.from(this);

  rv
}

predicate weirdo() 
 requires calid()
 ensures  MapOK(m)
 reads oHeap`fields, oHeap`fieldModes
 reads ns`fields, ns`fieldModes
 {
      reveal calid();
      assert calid();
      reveal calidObjects();
      assert calidObjects();
      assert ks == m.Keys;
      reveal calidMap();
      assert calidMap();
      assert MapOK(m);
  MapOK(m)
 }



opaque predicate {:onlyNUKE} AreWeNotMen(x : Object,  rv : Map)  //hmmm wgt etc?
      reads oHeap`fields, oHeap`fieldModes
      reads ns`fields, ns`fieldModes
      requires x in rv.m.Keys
   {
      && ((   (inside(x,rv.o))) ==> rv.m[x] in rv.ns)
     // &&     (inside(x,rv.o)) ==> (UniqueMapEntry(rv.m,x))
      && ((not(inside(x,rv.o))) ==> (rv.m[x] == x)) 
   }

lemma WeAreDevo()
  requires calid()
  ensures  forall k <- m.Keys :: AreWeNotMen(k,this)
  {
            reveal calid();
            assert calid();
            reveal calidOK();
            assert calidOK();
            reveal calidObjects();
            assert calidObjects();
            reveal calidMap();
            assert calidMap();
            reveal calidSheep();
            assert calidSheep();

            assert  forall k <- m.Keys :: AreWeNotMen(k,this);
  }


static lemma AintNoSunshine(x : Object, rv : Map)
//
    requires not(inside(x,rv.o))
    requires x !in rv.m.Keys

    requires rv.calid()
    requires forall k <- rv.m.Keys :: rv.AreWeNotMen(k,rv)
    requires x  in rv.oHeap
    requires x !in rv.ns

    ensures  x !in rv.m.Values
{
    assert rv.calid();

    reveal rv.calid();
    assert rv.calid();
    reveal AreWeNotMen();
    assert forall k <- rv.m.Keys :: rv.AreWeNotMen(k,rv);

    reveal rv.calidObjects();
    assert rv.calidObjects();  
    reveal rv.calidOK();
    assert rv.calidOK();
    reveal rv.calidOK();
    assert rv.calidOK();
    reveal rv.calidSheep();
    assert rv.calidSheep();


    forall k <- rv.m.Keys 
      ensures (x !in rv.m.Values)
      {
        if (inside(k,rv.o)) 
          { assert rv.AreWeNotMen(k, rv);
            assert (rv.m[k] in rv.ns);
            assert  x !in rv.ns;
            assert (rv.m[k] != x);
          } 
        else if (k != x)
          { 
            assert not(inside(k,rv.o));
            assert rv.AreWeNotMen(k, rv);
            assert (rv.m[k] == k);
            assert  rv.m[k] != x;
          } 
        else
          {
            assert k in rv.m.Keys;
            assert {:contradiction} k == x;
            assert {:contradiction} not(inside(k,rv.o));
            assert {:contradiction} rv.AreWeNotMen(k, rv);
            assert {:contradiction} rv.m[k] == k;
            assert {:contradiction} rv.m[k] == x; 
            assert {:contradiction} rv.m[x] == x;    
            assert {:contradiction} x in rv.m.Values;
            assert {:contradiction} x in rv.m.Keys;
            assert {:contradiction} false; 
          }
      }
}                                           



    opaque predicate {:onlyNUKE} calid()
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    // are we valid, my preciouw?
    /// { MOK(this) }  //FUK DAT
      {
        && calidObjects()
        && calidOK()
        && calidMap()
        && calidSheep()
      }

    opaque predicate  {:onlyNUKE} calidObjects()
      reads oHeap`fields, oHeap`fieldModes
      reads ns`fields, ns`fieldModes
       {
        && ks == m.Keys
        && vs == m.Values
        && o in oHeap
        && ks <= oHeap
        && ns !! oHeap

        && vs <= ns + oHeap
      }

    opaque predicate  {:onlyReadFrames} calidOK()
      reads oHeap`fields, oHeap`fieldModes
      reads ns`fields, ns`fieldModes
       {
        && (o in oHeap)
        && (ks <= oHeap)
        && (vs <= oHeap+ns)
        && COK(o, oHeap)
        && CallOK(oHeap)
        && CallOK(ks, oHeap)
        && CallOK(vs, oHeap+ns)
        && CallOK(ns, oHeap+ns)
       }


    opaque predicate  {:onlyNUKE} calidMap()
      reads oHeap`fields, oHeap`fieldModes
      reads ns`fields, ns`fieldModes
      requires calidObjects() && calidOK()
       {
        reveal calidObjects(); assert calidObjects();
        reveal calidOK(); assert calidOK();
        && MapOK(m) // potentiall should expand this out?
        && (forall x <- ks :: (not(inside(x,o)) ==> (m[x] == x)))
        && (forall x <- ks, oo <- x.AMFO :: m[oo] in m[x].AMFO)
       }

    opaque predicate  {:onlyNUKE} calidSheep2()
      reads oHeap`fields, oHeap`fieldModes
      reads ns`fields, ns`fieldModes
      requires calidObjects() && calidOK() && calidMap()
       {
        reveal calidObjects(); assert calidObjects();
        reveal calidOK(); assert calidOK();
        reveal calidMap(); assert calidMap();
        assert ks == m.Keys;
        
        && (forall x <- ks ::
           if (inside(x,o))
            then ((m[x] in ns) && (UniqueMapEntry(m,x))) 
            else  (m[x] == x))
        && (forall x <- ks :: x.fieldModes == m[x].fieldModes)         
        }
      

    opaque predicate {:onlyNuke} calidSheep()
      reads oHeap`fields, oHeap`fieldModes 
      reads ns`fields, ns`fieldModes
      requires calidObjects() && calidOK()// && calidMap()
       {
        reveal calidObjects(); assert calidObjects();
        reveal calidOK(); assert calidOK();
        //reveal calidMap(); assert calidMap();
        assert ks == m.Keys;

        reveal AreWeNotMen(); 
        //reveal UniqueMapEntry();
        
        && (forall x <- ks :: AreWeNotMen(x, this))
        && (forall x <- ks :: x.fieldModes == m[x].fieldModes)
       }
       


    opaque predicate {:onlyNUKE} calidSheep3()
      reads oHeap`fields, oHeap`fieldModes 
      reads ns`fields, ns`fieldModes
      requires calidObjects() && calidOK() && calidMap()
       {
        reveal calidObjects(); assert calidObjects();
        reveal calidOK(); assert calidOK();
        reveal calidMap(); assert calidMap();
        assert ks == m.Keys;
      
        && (forall x <- ks |    (inside(x,o)) :: (m[x] in ns))
        && (forall x <- ks |    (inside(x,o)) :: (UniqueMapEntry(m,x)))
        && (forall x <- ks | not(inside(x,o)) :: (m[x] == x))
        && (forall x <- ks :: x.fieldModes == m[x].fieldModes)        
       }
       
      



lemma {:onlyNUKE} sheep12() 
  requires calidObjects() && calidOK() && calidMap()
  requires calidSheep2()
  ensures  calidSheep()
  {
        reveal calidObjects(); assert calidObjects();
        reveal calidOK(); assert calidOK();
        reveal calidMap(); assert calidMap();
        reveal calidSheep(), calidSheep2();

        assert forall x <- ks :: 
          if (inside(x,o))
            then ((m[x] in ns) && (UniqueMapEntry(m,x))) 
            else  (m[x] == x);

        reveal AreWeNotMen();
        assert forall x <- ks :: AreWeNotMen(x, this);

        assert forall x <- ks :: x.fieldModes == m[x].fieldModes;

  }



} ///end datatype Map



lemma SubsetOfKeysOfExtendedMap(subset : set<Object>, left : Map, right : Map) 
  requires left.calid()
  requires right.calid()
  requires subset <= left.ks
  requires mapLEQ(left.m, right.m)
  ensures  subset <= right.ks
  {
    reveal Map.calid();
    reveal Map.calidObjects();
    assert left.calid();
    assert right.calid();
    assert left.calidObjects();
    assert right.calidObjects();
    assert mapLEQ(left.m, right.m);
    assert left.m.Keys <= right.m.Keys;
    assert subset <= left.ks <= right.ks;
  }


lemma Yowl(k : Object, kk : set<Object>)
  requires forall kx <- k.extra :: kx in kk
  ensures  k.extra <= kk
{}


lemma Howl(k : Object, kk : set<Object>)
  requires k.extra <= kk
  ensures  forall kx <- k.extra :: kx in kk
{}



///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
//actual cloning methods


method {:onlyCVM}   Clone_Via_Map(a : Object, m' : Map)
    returns (b : Object, m : Map)
//entry point for Clone - clones a according to map m'
//call with m' empty    
  decreases (m'.oHeap - m'.ks), a.AMFO, (a.fields.Keys), 20 //Clone_Via_Map

  requires m'.calid()
  requires a in m'.oHeap  //technically redundant given COKx
  requires COK(a, m'.oHeap)

  requires a.extra == {} //extra not yet cloned

  //ensures  (m.oHeap - m.ks) < (m'.oHeap - m'.ks) 

  ensures  m.calid()
  //includes CallOK(m.oHeap)
  //includes CallOK(m.ks, m.oHeap)
  //ensures  a.region.Heap? == b.region.Heap?
  
  ensures  a in m.ks
  ensures  a in m.m.Keys
  ensures  b in m.vs
  ensures  b in m.m.Values
  ensures  a in m.m.Keys && m.at(a) == b
  ensures  COK(b,m.oHeap+m.ns)

//should I package this up - as aw twostate or a onestate?
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.ks >= m'.ks + {a}
  ensures  m.vs >= m'.vs + {b}
  ensures  m.from(m')

  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns >= m'.ns
//  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
//  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert 
  ensures MapOK(m.m) 
  ensures a.AMFO <= m.ks  //seems weird but we are populating m, right...
  ensures a.extra <= m.ks //ditto?

  //ensures b.AMFO == set x <- a.AMFO :: m.m[x]


  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap+m'.ns)
//  ensures  unchanged(m'.oHeap)


  ensures b.fieldModes == a.fieldModes

//  ensures  fresh(b)
//modifies m'[a]
//  modifies m'.ns`fields //argh. pity so wide
//modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
// modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
modifies {} // only modifes objecst allocated aftrer this point?
{ 
  m := m';

  assert m.calid();

  assert  m.o     == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  m.ns    >= m'.ns;

  assert unchanged(a) && unchanged(m.oHeap);

  print "CALL Clone_Via_Map:", fmtobj(a), " owner:", fmtobj(m.o), "\n";

  print "VARIANT CVM ", |(m'.oHeap - m'.ks)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 20, "\n";

  assert COKSTART: COK(a, m.oHeap);

  print "Clone_Via_Map started on:", fmtobj(a), "\n";

//if already in hash table - return it and be done!
//not sure why this takes sooo long compared to other
  if (a in m.ks) { 

        assert (a in m.m.Keys) by {
            reveal m.calid();
            assert m.calid();
            reveal m.calidObjects();
            assert m.calidObjects();
            assert m.ks == m.m.Keys;            
        }

        b := m.m[a];
       
        assert (b in m.vs) by {
            reveal m.calid();
            assert m.calid();
            reveal m.calidObjects();
            assert m.calidObjects();
            assert b == m.m[a];
            assert b in m.m.Values;
            assert m.vs == m.m.Values; 
            assert b in m.vs;
        }

        assert CallOK(m.vs, m.oHeap+m.ns) by 
          {
            reveal m.calid();
            assert m.calid();
            reveal m.calidObjects();
            assert m.calidObjects();
            reveal m.calidOK();
            assert m.calidOK();
          }
            
        COKfromCallOK(b, m.vs, m.oHeap+m.ns);
        assert COK(b, m.oHeap+m.ns);
        print "RETN Clone_Via_Map: ", fmtobj(a)," already cloned,  returning ",fmtobj(b), "\n";



        assert MapOK(m.m) && (a.AMFO <= m.ks) && (a.extra <= m.ks)  by
          {
            reveal m.calid();
            assert m.calid();
            reveal m.calidOK();
            assert m.calidOK();
            reveal m.calidObjects();
            assert m.calidObjects();
            reveal m.calidMap();
            assert m.calidMap();
            assert m.ks == m.m.Keys;
            assert MapOK(m.m) && a.AMFO <= m.m.Keys;
            assert MapOK(m.m) && a.AMFO <= m.ks;
            assert a.extra <= m.ks;
          }

            reveal m.calid();
            assert m.calid();
            reveal m.calidSheep();
            assert m.calidSheep();

  assert  b.fieldModes == a.fieldModes;
  assert  m.o     == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  m.ns    >= m'.ns;
//  reveal  m.from();
      return;
  } // a in ks, already cloned

  assert unchanged(a) && unchanged(m.oHeap);

  assert a !in m.ks;
  assert a !in m'.ks;
  // assert a !in m.vs;
  // assert a !in m'.vs; 

///case analysis...
  if (outside(a,m.o)) {
   print "Clone_Via_Map ", fmtobj(a), " is really outside ", fmtobj(m.o), "so maps to itself (share not clone)\n";

      if (a.region.Heap?) {
        print "Clone_Via_Map outside owners:", fmtobj(a), " owned by ", fmtobj(a.region.owner) ,"\n";

        assert 
          && (a !in m.m.Keys)
          && (a !in m.ns) 
          && (m.m.Values == m.vs)
          by {
            reveal m.calid();
            assert m.calid();
            reveal m.calidOK();
            assert m.calidOK();
            reveal m.calidObjects();
            assert m.calidObjects();
            reveal m.calidMap();
            assert m.calidMap();
            assert m.ks == m.m.Keys;
            reveal m.calidSheep();
            assert m.calidSheep();
            assert a !in m.m.Keys; 
            assert a in m.oHeap;
            assert m.oHeap !! m.ns;
            assert a in m.oHeap;
            assert m.m.Values == m.vs;
        }

        m.WeAreDevo();
        Map.AintNoSunshine(a,m);

        assert a !in m.vs by {
            assert a !in m.m.Values;
            assert m.m.Values == m.vs;
            assert a !in m.vs;
        }
          b, m := Clone_Outside_Heap(a, m);


      //END outside  HEAP OBJECT
    } 
    else 
     {
        print "Clone_Via_Map world:", fmtobj(a),"\n";

        b, m := Clone_Outside_World(a, m);

      }//end of outside / world 

  assert m.m[a] == b;

  assert  m.o     == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  m.ns    >= m'.ns;

  assert m.calid();
  reveal m.calid();
  assert m.calidObjects();
  assert m.calidOK();
  reveal m.calidSheep();
  assert m.calidSheep();

  assert a in m.ks;
  assert b.fieldModes == a.fieldModes;

      assert forall kx <- a.extra :: m.m[kx] in m.m[a].extra;
      assert a.extra <= m.ks;

  return;  //we may as well just return here.
           //we've done all we need to do.  I think.

 }///END OF THE OUTSIDE CASE
 else 
 { //start of the Inside case 

  if (a.region.Heap?) {  //start of inside heap case
        print "Clone_Via_Map owners:", fmtobj(a), " owned by ", fmtobj(a.region.owner) ,"\n";

        b, m := Clone_Inside_Heap(a, m);
      //  assert b.fields.Keys == {};  //we now do clone fields though!!

      //END inside HEAP OBJECT 
    } else {
      //inside "world"" OBJECT

      b, m := Clone_Inside_World(a, m);
    //  assert b.fields.Keys == {};

    }   //end of inside world heap case
 } //end of inside case 
 

///////////////////////////////////////////////////////////////
//tidying up after the cases..

  reveal m.calid();
  assert m.calid();
  reveal m.calidObjects();
  assert m.calidObjects();
  reveal m.calidOK();
  assert m.calidOK();
  assert CallOK(m.vs, m.oHeap+m.ns);
  assert b in m.m.Values; 
  assert m.m.Values == m.vs;
  assert b in m.vs;
  COKfromCallOK(b, m.vs, m.oHeap+m.ns);
  assert COK(b, m.oHeap+m.ns);
//  assert fresh(b);   //umm, yeah should probalboy be fresh at least if INSIDE, but...
//  have to experiment with a clause somewhere in calidSheep saying every inside clone is new
//  or everyhing in ns is new. or...
  assert b in m.ns;

  assert m.m[a] == b;
  assert a !in m'.ks;
  assert b !in m'.oHeap;
  //assert b !in m'.ns;


//  assert  b.fields.Keys == {};

  assert  b.fieldModes.Keys == a.fieldModes.Keys;

  reveal m.calidSheep();
  assert m.calidSheep();

  assert  b.fieldModes == a.fieldModes;

//  assert m.from(m') by {
//      reveal m.from();
      assert  m.o     == m'.o;
      assert  m.oHeap == m'.oHeap;
      assert  m.ns    >= m'.ns;
    
      assert m.from(m');
//  }
}







method  {:onlyCFM} Clone_All_Fields(a : Object, b : Object, m' : Map) 
   returns (m : Map)
//clone field a.n into b.n
//a should be preexisting (in m'.oHeapl); b should be "new"  in m'.ns

  decreases (m'.oHeap - m'.ks +{a}), a.AMFO, (a.fields.Keys), 10 //Clone_All_Fields

  requires m'.calid()
  requires COK(a, m'.oHeap)
  requires COK(b, m'.oHeap+m'.ns)

  requires b.fields.Keys == {}

  requires a.fields.Keys <= a.fieldModes.Keys
  requires a.fieldModes == b.fieldModes

 
  requires a in m'.oHeap  
  requires a in m'.ks

  requires b in m'.vs
  requires b in m'.ns
  requires (a in m'.m.Keys) && m'.m[a] == b
  requires m'.o    in m'.oHeap
  requires m'.ks   <= m'.oHeap


  // requires b.fieldModes[n] == Evil //evilKJX this is actually evil 
                                   //well not *that* evil as I still must satisfy refOK
  //  
  // requires forall n <- b.fields :: (n in b.fieldModes) &&
  //             AssignmentCompatible(b, b.fieldModes[n], b.fields[n])

  //consequently
//   requires refOK(a, a.fields[n])
   requires a.region.Heap? == b.region.Heap?




  ensures  m.calid()
  ensures  b.fields.Keys == a.fields.Keys

  ensures  a in m.ks
  ensures  (a in m.m.Keys) && m.m[a] == b

  

//   ensures  n in b.fields
//   ensures  (a.fields[n] in m.m.Keys) && m.m[a.fields[n]] == b.fields[n]

  ensures  b in m.vs

  ensures  mapLEQ(m'.m,m.m)
  
  ensures  CallOK(m.oHeap)
  ensures  COK(a, m.oHeap)
  ensures  COK(b, m.oHeap+m.ns)
  ensures  CallOK(m.vs, m.oHeap+m.ns)
  ensures  CallOK(m.ns, m.oHeap+m.ns)

  ensures  m.o     == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns    >= m'.ns
  ensures  m.ks    <= m.oHeap 

  ensures a.fieldModes == b.fieldModes
  ensures b.fields.Keys == a.fields.Keys

  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap)
//  ensures unchanged(m.vs - {b}) //duesb;t veruft....

//  modifies (set o : Object | o !in m'.oHeap)`fields
// modifies (set o : Object | o !in ((m'.oHeap+m'.ns) - {b}))`fields
  //or can this  be modifies m'.ns? 
  modifies b`fields   ///GGRRR
  {
    m := m';

assert BINNS:  b in m.ns;
print "VARIANT CAF ", |(m'.oHeap - m'.ks +{a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 10, "\n";
print "<<<<<<<<<<<\n";
print "just cloned ", fmtobj(a), " as ", fmtobj(b), "\n";
print "<<<<<<<<<<<\n";


  assert unchanged(a) && unchanged(m.oHeap);

  assert  m.o == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  m.ns == m'.ns;
  assert  m.vs == m'.vs;

  assert  m.ks == m'.ks;
  assert  a in m'.ks;

  assert m.m[a] == b;  //mmmKJX
  // assert (a in m.ks) ==> (m[a] == b);  //mmmKJX

  assert m.calid();
  assert COK(b, m.oHeap+m.ns);
  assert HEREB: COK(b, m.oHeap+m.ns);
  



//assert fresh(b);
assert  b.fields.Keys == {}; 
assert b in m.vs;

//START OF FIELDS…

print "<<<<<<<<<<<\n";
printmapping(m.m);
print "<<<<<<<<<<<\n";

  assert m.calid();

  var ns : seq<string> := set2seq(a.fields.Keys);

assert forall k <- a.fields.Keys :: (multiset(a.fields.Keys))[k] == 1;
assert forall s <- ns :: (multiset(ns))[s] == 1;
assert forall i | 0 <= i < |ns|, j | 0 <= j < |ns| :: (ns[i] == ns[j]) <==> i == j;
//assert b.fields.Keys == {};
assert b.fields.Keys == seq2set(ns[..0]);


  print "Clone_All_Fields fields:", fmtobj(a), " fields=", fmtseqstr(ns), "\n";  

//DOING FIELDS≈≈

  print "BLOOP BLOOP BLOOP\n";

 assert m.calidOK() by { 
  assert m.calid(); 
  reveal m.calid();
  assert m.calidOK();
  }

  assert COK(b, m.oHeap+m.ns);
  
label BLOOP:

  assert m.calidOK();
  reveal m.calidOK();
  assert m.calid();
     assert CallOK(m.ns, m.oHeap+m.ns);
     assert CallOK(m.vs, m.oHeap+m.ns);

     assert CallOK(m.ks, m.oHeap) by {}



var rm := m;

  assert  rm.o     == m.o      == m'.o;    
  assert  rm.oHeap == m.oHeap  == m'.oHeap;
  assert  rm.ns    >= m.ns     >= m'.ns;   
  assert  rm.vs    >= m.vs     >= m'.vs; 
  assert  m.ks     <= rm.ks    <= m.oHeap;
  

COKgetsDeclaredFields(a, m.oHeap);
  assert unchanged(a) && unchanged(m.oHeap);
  assert CallOK(m.ks, m.oHeap); 
     

  for i := 0 to |ns| 

     invariant  rm.o     == m.o      == m'.o 
     invariant  rm.oHeap == m.oHeap  == m'.oHeap
     invariant  rm.ns    >= m.ns     >= m'.ns  
     invariant  rm.vs    >= m.vs     >= m'.vs
     invariant   m.ks    <= rm.ks    <= m.oHeap
  
     invariant  b in m.ns
     invariant  b in m.vs

     invariant COK(a, m.oHeap)
     invariant COK(b, m.oHeap+m.ns)
     invariant mapLEQ(m'.m,m.m)
     invariant a in m.oHeap
     invariant a in m.ks
     invariant m.o in m.oHeap
     invariant CallOK(m.oHeap)
     invariant CallOK(m.ks, m.oHeap)
     invariant CallOK(m.ns, m.oHeap+m.ns)
     invariant CallOK(m.vs, m.oHeap+m.ns)
     invariant m.calid()
     invariant unchanged(a) 
     invariant unchanged(m.oHeap)
     //invariant forall x <- m.ks :: (not(inside(x,m.o)) ==> (m.at(x) == x)) 
     invariant (m'.oHeap - m'.ks +{a}) >= (m.oHeap - m.ks +{a})
     invariant (m'.oHeap - m'.ks) >= (m.oHeap - m.ks)
     invariant b.fields.Keys == seq2set(ns[..i])
     invariant forall i | 0 <= i < |ns|, j | 0 <= j < |ns| :: (ns[i] == ns[j]) <==> i == j

     invariant  m.m[a] == b
     invariant  a.fieldModes == b.fieldModes
     invariant  a.AllFieldsAreDeclared()
 

   {


assert b.fields.Keys == seq2set(ns[..i]);

      assert COK(b, m.oHeap+m.ns);

        var n : string := ns[i];
        var ofv : Object := a.fields[n];   

    assert n !in seq2set(ns[..i]);

    assert (n !in b.fields.Keys) by {
        assert n !in seq2set(ns[..i]);
        assert b.fields.Keys == seq2set(ns[..i]);
        assert (n !in b.fields.Keys);
    }

    print "  TLOOP  ",fmtobj(a),".",n," :=", fmtobj(ofv), "\n";
    print "  TLOOP  (recurse on field ",n,")\n";
    print "  TLOOP m:", |m.oHeap - m.ks|, " m':", |m'.oHeap - m'.ks|, "\n";
    print "  TLOOP b.fieldsKeys==", b.fields.Keys, "\n";
    print "  TINV                ", ns[..i], "\n";
    print "  TLOOPINV            ",seq2set(ns[..i]),"\n";


print "VARIANT*CAF ", |(m'.oHeap - m'.ks +{a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 10, "\n";


//   assert (m.oHeap - m.ks) < (m'.oHeap - m'.ks);


  assert  rm.o     == m.o      == m'.o;    
  assert  rm.oHeap == m.oHeap  == m'.oHeap;
  assert  rm.ns    >= m.ns     >= m'.ns;   
  assert  rm.vs    >= m.vs     >= m'.vs; 
  assert  m.ks     <= rm.ks    <= m.oHeap;
  

assert b in m.ns by { reveal BINNS; assert b in m.ns; }
assert n !in b.fields;
assert refOK(a, a.fields[n])
 by {
     assert m.calid();  reveal m.calid();
     assert m.calidOK(); reveal m.calidOK();
     assert COK(a,m.oHeap); reveal COK();
     assert a.AllOutgoingReferencesAreOwnership(m.oHeap);
  assert  refOK(a, a.fields[n]);
  // - inside(f,t.region.owner);
 }

assert a.AllFieldsAreDeclared();
assert a.fields.Keys <= a.fieldModes.Keys;
assert a.fieldModes == b.fieldModes;
assert n in b.fieldModes;


assert forall n <- b.fields :: 
   && (n in b.fieldModes) 
   && AssignmentCompatible(b, b.fieldModes[n], b.fields[n])
by {
  assert m.calid();
  reveal m.calid();
  assert COK(b, m.oHeap+m.ns);
  reveal COK();
  assert b.Valid();
  assert b.AllFieldsContentsConsistentWithTheirDeclaration();
  assert forall n <- b.fields :: 
      AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);
}

         var OLDFLDS := b.fields.Keys;

  assert b in m.ns;
  assert b in m.vs;
  assert a in m.ks;



  var v_caf := ((m'.oHeap - m'.ks +{a}), a.AMFO, (a.fields.Keys), 10);
  var v_cfm := ((m.oHeap - m.ks +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Clone_Field_Map

print "v_caf ", v_caf, "\n";
print "v_cfm ", v_cfm, "\n";

assert b.fields.Keys == seq2set(ns[..i]);
assert a.fields.Keys == seq2set(ns);

print "okaoka ", (m'.oHeap - m'.ks +{a}) >  (m.oHeap - m.ks +{a}), "\n";
print "okaoka ", (m'.oHeap - m'.ks +{a}) == (m.oHeap - m.ks +{a}), "\n";

assert (m'.oHeap - m'.ks +{a}) >= (m.oHeap - m.ks +{a});
assert a.AMFO >= a.AMFO;
assert (a.fields.Keys) >= (a.fields.Keys - b.fields.Keys);
assert 10 > 5;


  rm := Clone_Field_Map(a,n,b,m);
      


  assert  rm.o     == m.o      == m'.o;    
  assert  rm.oHeap == m.oHeap  == m'.oHeap;
  assert  rm.ns    >= m.ns     >= m'.ns;   
  assert  rm.vs    >= m.vs     >= m'.vs; 
  assert  m.ks     <= rm.ks    <= m.oHeap;
  
        assert b.fields.Keys == OLDFLDS + {n};


assert b.fields.Keys == seq2set(ns[..i+1]);

assert rm.calid();
//  assert COK(b, m.oHeap+m.ns);
  m := rm;
assert m.calid();

assert  CallOK(m.ks, m.oHeap) 
  by { reveal m.calid();    assert m.calid();
       reveal m.calidOK();  assert m.calidOK();
   }


      } //end of loop

  assert unchanged(a) && unchanged(m.oHeap);


  //DONE FIELDS
     print "RETN Clone_All_Fields done ", fmtobj(a), "\n";

  assert COK(b, m.oHeap+m.ns) by { reveal HEREB; }
  assert mapLEQ(m'.m,m.m);

reveal m.calid();
assert m.calid();
reveal m.calidObjects();
assert m.calidObjects();

  reveal m.calidMap(); assert m.calidMap();
  reveal m.calidSheep(); assert m.calidSheep();


  assert m.m[a] == b;  //kjxFIX

  assert m.at(a) == b;  //kjxFIX
  assert a in m.ks;  //kjxFIX
  assert b in m.oHeap+m.ns;//kjxFIX

  assert COK(b, m.oHeap+m.ns);

    assert mapLEQ(m'.m,m.m);
 
  
    assert CallOK(m.oHeap);
    assert COK(a, m.oHeap);
    assert COK(b, m.oHeap + m.ns);
    assert CallOK(m.vs, m.oHeap+m.ns);
    assert COK(b, m.oHeap  + m.ns);

 
    reveal m.calidObjects(); assert m.calidObjects();


        assert COK(m.o, m.oHeap);
        assert CallOK(m.oHeap);
        assert CallOK(m.ks, m.oHeap);
        assert CallOK(m.vs, m.oHeap+m.ns);
        assert CallOK(m.ns, m.oHeap+m.ns);

    reveal m.calidOK(); assert m.calidOK();

    reveal m.calidMap(); assert m.calidMap();

    assert MapOK(m.m);


    
  assert  rm.o     == m.o      == m'.o;  
  assert  rm.oHeap == m.oHeap  == m'.oHeap;
  assert  rm.ns    >= m.ns     >= m'.ns; 
  assert  rm.vs    >= m.vs     >= m'.vs; 

    reveal m.calidObjects(); assert m.calidObjects();
    reveal m.calidOK(); assert m.calidOK();
    reveal m.calidSheep(); assert m.calidSheep();
    
    assert m.ks == m.m.Keys;

    reveal m.AreWeNotMen(); 
    assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);
    assert forall x <- m.ks :: (not(inside(x,m.o)) ==> (m.m[x] == x));

    assert  b.fieldModes == a.fieldModes;

    reveal m.calid(); assert m.calid();

    assert MapOK(m.m) && a.AMFO <= m.ks;
      assert unchanged(a) && unchanged(m.oHeap);
  
    return;
}//end Clone_All_Fields
 




method {:isolate_assertions} {:timeLimit 40} Clone_Outside_Heap(a : Object, m' : Map)
      returns (b : Object, m : Map)
  decreases (m'.oHeap - m'.ks), a.AMFO, (a.fields.Keys), 15 //Clone_Outside_Heap

  requires a.extra == {} //extra not yet cloned

//this case
  requires a !in m'.ks
  requires a !in m'.vs

  requires outside(a,m'.o)
  requires a.region.Heap?

//all Clone_
  requires m'.calid()
  requires a in m'.oHeap 
  requires COK(a, m'.oHeap)
  
  ensures  m.calid()
  ensures  a == b
  ensures  a in m.ks
  ensures  a in m.m.Keys
  ensures  b in m.vs
  ensures  b in m.m.Values
  ensures  a in m.m.Keys && m.at(a) == b
  ensures  COK(b, m.oHeap+m.ns)

//should I package this up - as aw twostate or a onestate?
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.ks >= m'.ks + {a}
  ensures  m.vs >= m'.vs + {b}
  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns >= m'.ns
//  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
//  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert 
  ensures MapOK(m.m) 
  ensures a.AMFO <= m.ks  //seems weird but we are populating m, right...
  ensures a.extra <= m.ks //ditto?

  //ensures b.AMFO == set x <- a.AMFO :: m.m[x] 

  ensures b.fieldModes == a.fieldModes
//  ensures b.fields.Keys == a.fields.Keys

//  modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  modifies {}
  {
        m := m';
        assert m.ks == m'.ks;
        assert a !in m.ks;
        assert a !in m.vs;

        assert m == m';
        assert m.m == m'.m;
        assert mapLEQ(m'.m,m.m);
        assert m.from(m');

        print "Clone_Outside_Heap outside owners:", fmtobj(a), " owned by ", fmtobj(a.region.owner) ,"\n";
print "VARIANT COH ", |(m'.oHeap - m'.ks)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";

    assert CallOK(m.oHeap) by {
          reveal m.calid();
          assert m.calid();
          reveal m.calidOK();
          assert m.calidOK();
          reveal CallOK();
          assert CallOK(m.oHeap);
        }

    assert (a.Ready() && a.Valid()) by {
          reveal CallOK();
          assert CallOK(m.oHeap);
          assert a in m.oHeap;
          COKfromCallOK(a, m.oHeap);
          reveal COK();
          assert COK(a, m.oHeap);  
          assert a.Ready();
          assert a.Valid();
       } 


   assert a.OwnersValid() by {
          assert a.Ready();
          assert a.Valid();
          assert a.OwnersValid();
       } 


        assert COK(a.region.owner, m.oHeap) by {
            assert a.OwnersValid();
            assert a.AMFO > a.region.owner.AMFO;
            assert CallOK(m.oHeap);
            COKfromCallOK(a, m.oHeap);
            reveal COK();
            assert COK(a, m.oHeap);
            a.CallMyOwnersWillWitherAway(a, m.oHeap);
            assert COK(a.region.owner, m.oHeap); 
          }

    assert CallOK(a.extra, m.oHeap) by {
      assert a.OwnersValid();
            assert a.extra <= a.AMFO;
            assert CallOK(m.oHeap);
            assert COK(a,m.oHeap);
            assert a.extra <= m.oHeap by {
                assert COK(a,m.oHeap);
                reveal COK();
                assert a.extra <= m.oHeap;
            }
            CallOKNarrowFocus(a.extra, m.oHeap);
            reveal CallOK();
            assert COK(a, m.oHeap);
            a.CallMyOwnersWillWitherAway(a, m.oHeap);
            assert CallOK(a.extra, m.oHeap); 
    }


//preconditions for the call..
  // assert m.calid();
  // assert a.region.owner in m.oHeap;  
assert COK(a.region.owner, m.oHeap); 
  // assert outside(a.region.owner, m.o); //TEMP TO WRITEOUTSIDE CASE

reveal COK(); assert a.extra == {}; //extra not yet cloned

        var rowner, rm := Clone_Via_Map(a.region.owner, m);
        assert a.region.owner in rm.ks;
        assert a.region.owner.AMFO <= rm.ks;
        assert a.AMFO == a.region.owner.AMFO + a.extra + {a};
        assert rm.from(m);
        assert rm.from(m');
assert MapOK(rm.m); 
reveal rm.calid(); assert rm.calid();
reveal rm.calidObjects(); assert rm.calidObjects();
        assert rm.ks == rm.m.Keys;
reveal rm.calidMap(); assert  rm.calidMap(); 
        assert (forall x <- rm.m.Keys, oo <- x.AMFO :: rm.m[oo] in rm.m[x].AMFO);
        assert (forall x <- rm.ks,     oo <- x.AMFO :: rm.m[oo] in rm.m[x].AMFO);
        assert rm.ks >= m'.ks;
        assert mapLEQ(m'.m,rm.m);    
        assert rm.from(m);

///WHY THE FuCK DO I NEED TO DO THIS?
///BEST GUESS TO EnSURE ALL The OWNERS of a are in the map
///becuse it's outside it shouldn't actually CLONE ANYTHING

        ///BUT things hop around insidef, e.g. so we've already copied "a" in the recursive call
        ///can we just be done?
        ///Hmm. fuck I hate this shit

      //Hmm do we even need to do this?
      //or won't the recursive call handle it anyway??
        if (a in rm.ks) {
            m := rm;
            assert m.from(rm);  
            reveal m.calid();
            assert m.calid();  
            reveal m.calidObjects();
            assert m.calidObjects();  
            reveal m.calidSheep();
            assert m.calidSheep();

            assert m.at(a).fieldModes == a.fieldModes;
            b := m.at(a);
            assert b == m.m[a];

            assert (b == a) by {
              assert not(inside(a, m.o));   //glurk
              reveal m.AreWeNotMen();
              assert m.AreWeNotMen(a,m);
              assert ((not(inside(a, m.o))) ==> (m.m[a] == a));
              assert (m.m[a] == a);
              assert (m.m[a] == m.at(a) == a);
              assert b == a;      //double glurk 
            }

            assert b.fieldModes == a.fieldModes;

            reveal m.calidOK();
            assert m.calidOK();
            assert CallOK(m.vs, m.oHeap+m.ns);
            assert b in m.m.Values; 
            assert m.m.Values == m.vs;
            assert b in m.vs;
            COKfromCallOK(b, m.vs, m.oHeap+m.ns);
            assert COK(b, m.oHeap+m.ns);

            assert b.fieldModes == a.fieldModes;
            assert m.from(m');
            return; //should work because Clone_Via_Map meets all the conditiosn, right???
        }  //end if a in rm.ks
 

        assert a !in rm.ks; 
        assert a !in rm.vs by { 
          
          
                assert not(inside(a,rm.o));
                assert a !in rm.m.Keys;
                assert rm.calid(); 
                rm.WeAreDevo();
                assert forall k <- rm.m.Keys :: rm.AreWeNotMen(k,rm);
                assert a  in rm.oHeap;
                assert a !in rm.ns;
          
          
          
          Map.AintNoSunshine(a, rm);
          assert a !in rm.vs; }
        assert rm.ks >= m'.ks;
        assert mapLEQ(m'.m,rm.m);
        assert rm.from(m');

//    //maintaing MapOK
//         assert AMFOOKRM: a.owners() <= rm.ks by {
//             reveal rm.calid();
//             assert rm.calid();
//             reveal rm.calidMap();
//             assert rm.calidMap();
//             assert MapOK(rm.m);
//             reveal rm.calidObjects();
//             assert rm.calidObjects();             
//             assert (forall x <- rm.ks, oo <- x.AMFO :: oo in rm.ks);
//             assert a.owners() <= rm.ks by {
//                reveal COK(); 
//                assert COK(a,m.oHeap); 
//                assert a.AMFO <= m.oHeap;
// //               assert a.owners() <= rm.ks;
//                }
//         }5



        assert a in rm.oHeap; 
        assert COK(a, rm.oHeap);
        reveal COK();
        assert a.AMFO <= rm.oHeap;
      //  assert a.owners() <= rm.ks;
        OutsidersArentMapValues(a,rm);
        assert a !in rm.vs;
        assert a !in rm.ks;
        assert not(inside(a, rm.o)); 

        //m := rm[a:=b];     


        assert COK(a, rm.oHeap);

        assert rm.calid();
        assert a in rm.oHeap;
        assert COK(a, rm.oHeap);
        assert a.extra <= rm.oHeap; 

        assert CallOK(rm.oHeap) by {
          reveal rm.calid(), rm.calidOK();
          assert rm.calid();
          assert rm.calidOK();
          reveal CallOK(), COK();
          assert CallOK(rm.oHeap);
        }


        var xm := rm;
        assert xm.ks >= m'.ks;
        assert mapLEQ(m'.m,xm.m);    
        assert xm.from(rm);
        assert xm.from(m');

        assert a !in xm.ks;
        assert a !in xm.vs;


        var MX := a.extra - xm.ks;
        assert MX <= a.extra;
        var xo : Object;
        var rr : Object;
        var oldmks  : set<Object>;  //dont fucking ask
        var oldmok :=  false;

        assert !oldmok;
        assert xm == rm;
        assert xm.ks >= (m'.ks);
        assert mapLEQ(m'.m,xm.m);    
        assert xm.from(m');

        assert a !in xm.ks;

        while ((MX != {}) && (a !in xm.ks))
          decreases MX
          invariant MX == a.extra - xm.ks
          invariant MX <= a.extra
          invariant xm == rm
          invariant xm.calid()
          invariant rm.calid()
          invariant m'.calid()
          invariant xm.from(m')  
          invariant MX <= xm.oHeap            
          invariant CallOK(xm.oHeap)    
          invariant a.AMFO - {a} <= xm.ks + MX
          invariant a.extra <= a.AMFO
          invariant oldmok ==> assigned(oldmks)
          invariant oldmok ==> (xm.ks > oldmks)
          invariant m'.oHeap == xm.oHeap
          invariant oldmok ==> ((m'.oHeap - oldmks) > (xm.oHeap - xm.ks))
          invariant xm.ks >= (m'.ks)
          invariant xm.vs >= (m'.vs)
          invariant a !in xm.ks
        {
          assert xm == rm;
          xo :| xo in MX;
          assert xo in MX;
          MX := MX - {xo};
           
          assert xm.calid();
          assert xo in xm.oHeap;
          COKfromCallOK(xo,xm.oHeap);
          assert COK(xo,xm.oHeap);
          assert xo !in xm.ks;
        
        
          assert oldmok ==> (m'.oHeap - oldmks) > (xm.oHeap - xm.ks);

assert xo in a.AMFO;
assert a.Ready();
assert xo in a.extra;
assert a.AMFO > xo.AMFO;


          assert (m'.oHeap) == m'.oHeap == xm.oHeap;
          assert xm.ks >= (m'.ks);
          assert xm.from(m');

  assert  mapLEQ(m'.m,xm.m) by 
               { reveal xm.calid(); assert xm.calid();
                 reveal xm.calidObjects(); assert xm.calidObjects();
                 assert m'.ks <= xm.ks;
                 assert m'.vs <= xm.vs; 
                 assert m'.ks == m'.m.Keys;
                 assert m'.vs == m'.m.Values;       
                 assert xm.ks == xm.m.Keys;
                 assert xm.vs == xm.m.Values;                              
                 assert m'.m.Keys <= xm.m.Keys;
                 assert m'.m.Values <= xm.m.Values;
                 assert forall k <- m'.m.Keys :: k in xm.m.Keys;
      assert forall k <- m'.m.Keys :: k in xm.m.Keys && (m'.m[k] == xm.m[k]);
                }
        

                  assert xm.ks >= m'.ks;
                assert a !in xm.ks;          

          assert ((m'.oHeap - m'.ks)) >= (xm.oHeap - xm.ks);

assert  ((a.AMFO)
  decreases to
        (xo.AMFO));
      
        assert ((m'.oHeap - m'.ks), 
               (a.AMFO),
               (a.fields.Keys), 
               (15) 
          decreases to 
               xm.oHeap - xm.ks, 
               xo.AMFO, 
               xo.fields.Keys, 
               20);

      
          rr, rm := Clone_Via_Map(xo, xm);
          assert rm.ks >= m'.ks;
          assert mapLEQ(m'.m,rm.m);    
          assert rm.from(m');

      if (a in rm.ks) { 
                m := rm;
                assert m.calidObjects() by {  reveal m.calid(); assert  m.calid();  }
                assert  a in m.ks by { reveal m.calidObjects(); assert m.calidObjects(); }
                assert  a in m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
                b := m.m[a];
                //

                assert  b in m.vs by { reveal m.calidObjects(); assert m.calidObjects();  assert b in m.m.Values; }
                assert  b in m.m.Values by { reveal m.calidObjects(); assert m.calidObjects(); }
                assert m.calidOK() by {  reveal m.calid(); assert  m.calid();  }
                assert  a in m.m.Keys && m.at(a) == b; 
                assert  COK(b, m.oHeap+m.ns) by {
                assert b in m.vs;
                assert CallOK(m.vs, m.oHeap+m.ns) by { reveal m.calidOK(); }
                COKfromCallOK(b, m.vs, m.oHeap+m.ns);   }

                assert m.from(m');

                assert  mapLEQ(m'.m,m.m) by 
                        { reveal m.calidObjects(); assert m.calidObjects();
                          assert m'.ks <= m.ks;
                          assert mapLEQ(m'.m,m.m);    
                          assert m'.m.Keys <= m.m.Keys;
                          assert m'.m.Values <= m.m.Values;
                          }
                assert  m.ks >= m'.ks + {a} by { reveal m.calidObjects(); assert m.calidObjects(); }
                assert  m.vs >= m'.vs + {b} by { reveal m.calidObjects(); assert m.calidObjects(); }
                assert  m.o == m'.o;
                assert  m.oHeap == m'.oHeap;
                assert  m.ns >= m'.ns;
                assert MapOK(m.m);
                assert forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys;
                assert  a in m.m.Keys;
                assert forall oo <- a.AMFO :: oo in m.m.Keys;
                assert a.AMFO <= m.m.Keys;
                assert m.ks == m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
                assert a.AMFO <= m.ks;
                assert a.extra <= m.ks;


            
                assert  a == b by {
                      reveal m.calid();
                      assert m.calidMap();
                      reveal m.calidMap();
                  //    assert (forall x <- m.ks :: (not(inside(x,m.o)) ==> (m.m[x] == x)));
                      assert not(inside(a,m.o));
                      assert m.m[a] == a;
                      assert a == b;
                  }

             assert (b.fieldModes == a.fieldModes) by { assert a == b; }
                      
              return; 
      }  // if a is in ks after clone -- if it got added magically...

          assert xo in rm.ks;
          assert xm != rm;
      //    assert rr == xo;

          MX := MX - rm.ks;
          assert rm.ks > xm.ks;
          oldmks := xm.ks;
          oldmok := true;
          xm := rm;
          assert xm.ks >= m'.ks;       
          assert xm.ks > oldmks;

          assert xm.from(m');


//          MX := a.extra - rm.ks;          
          assert xm == rm;
        } // end loop MX


        assert xm == rm;
        assert xm.ks >= m'.ks;      
        assert a !in xm.ks;    
        assert (a.AMFO - {a})<= xm.ks;
        assert a.extra <= a.AMFO;
        assert a !in a.extra;
        assert a.extra <= (a.AMFO - {a});
        assert a.extra <= (a.AMFO - {a}) <= xm.ks;
        assert a.extra <= xm.ks;
  
        assert xm.calid(); assert rm.calid();
        assert a.AMFO - {a} - a.extra <= rm.ks; 
      //  SubsetOfKeysOfExtendedMap(a.AMFO , rm, m);
        assert a.extra <= rm.ks;        
        assert a.owners() ==  a.AMFO - {a};
        assert a.AMFO == a.region.owner.AMFO + a.extra + {a};
        assert a.owners() <= rm.ks;
        assert xm.ks >= m'.ks;   
        assert xm.from(m');
        assert a !in xm.ks;

        assert a !in xm.m.Keys by { assert a !in xm.ks; }
        assert COK(a,xm.oHeap);
        assert a.Ready();
        assert a.AllOwnersAreWithinThisHeap(xm.ks);
        assert a.owners() <= xm.ks;
        assert (a.AMFO - {a}) <= xm.ks;
        assert (forall oo <- (a.AMFO - {a}) :: oo in xm.m.Keys);
      //  assert (a.region.Heap? ==> xm.m[a].region.Heap?);
        assert (a.region.Heap? ==> a.region.owner in a.AMFO);
        assert (a.region.Heap? ==> a.region.owner in xm.m.Keys);
      //  assert (a.region.Heap? ==> xm.m[a.region.owner] == xm.m[a].region.owner );
      //  assert (forall oo <- a.AMFO :: xm.m[oo] in xm.m[a].AMFO);
        assert (a.region.Heap? ==> a.extra <= a.AMFO);
        assert (forall xo <- a.extra :: xo in xm.m.Keys);
      //  assert (forall xo <- a.extra :: xm.m[xo] in xm.m[a].extra) ;

        assert a !in rm.ks;
        rm.WeAreDevo();
        assert a !in rm.vs  by { Map.AintNoSunshine(a, rm); }
        m := rm.putOutside(a);  
        b := m.at(a);
        assert b == a;
        assert b.fieldModes == a.fieldModes;


        assert m.at(a).fieldModes == a.fieldModes;
        b := m.at(a);
        assert b == m.m[a];

        assert (b == a) by {
          assert not(inside(a, m.o));   //glurk
          reveal m.AreWeNotMen();
          assert m.AreWeNotMen(a,m);
          assert ((not(inside(a, m.o))) ==> (m.m[a] == a));
          assert (m.m[a] == a);
          assert (m.m[a] == m.at(a) == a);
          assert b == a;      //double glurk 
        }

        assert COK(b, m.oHeap);
        COKWiderContext(b, m.oHeap, m.ns);
        assert COK(b, m.oHeap+m.ns);

        assert m.m == MappingPlusOneKeyValue(rm.m,a,b);
        assert m.calid(); 
        MapOKFromCalid(m);
        assert MapOK(m.m);
        assert mapLEQ(rm.m, m.m);
        assert m.from(rm);  assert m.from(m');    
    //    assert a.owners() <= rm.ks by { reveal AMFOOKRM; }
    assert a.AMFO - {a} - a.extra <= rm.ks; 
  //      SubsetOfKeysOfExtendedMap(a.AMFO, rm, m);
        assert a.owners() <= m.ks;

        assert b.fieldModes == a.fieldModes;

      //END outside  HEAP OBJECT
  }



method Clone_Outside_World(a : Object, m' : Map)
      returns (b : Object, m : Map)
  decreases (m'.oHeap - m'.ks), a.AMFO, (a.fields.Keys), 15 //Clone_Outside_World

  requires a.extra == {} //extra not yet cloned

//this case 
  requires a !in m'.ks
  requires outside(a,m'.o)
  requires a.region.World?

//all Clone_
  requires m'.calid()
  requires a in m'.oHeap 
  requires COK(a, m'.oHeap)


  ensures  m.calid()
  ensures  a in m.ks
  ensures  a in m.m.Keys
  ensures  b in m.vs
  ensures  b in m.m.Values
  ensures  a in m.m.Keys && m.at(a) == b
  ensures  COK(b, m.oHeap+m.ns)

//should I package this up - as aw twostate or a onestate?
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.ks >= m'.ks + {a}
  ensures  m.vs >= m'.vs + {b}
  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns >= m'.ns
//  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
//  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert 
  ensures MapOK(m.m) 
  ensures a.AMFO <= m.ks  //seems weird but we are populating m, right...
  ensures a.extra <= m.ks //ditto?
  //ensures b.AMFO == set x <- a.AMFO :: m.m[x] 

  ensures a.fieldModes == b.fieldModes
 // ensures b.fields.Keys == a.fields.Keys
  // modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  modifies {}
{
        m := m';


        assert ANKS: a !in m.ks;        

        assert COK(a,m.oHeap);
        reveal COK();
        assert a.Ready();
        assert a.AMFO == {a};

        reveal m.calid();
        assert m.calid(); 
        reveal m.calidOK();
        assert m.calidOK(); 
        reveal m.calidSheep();
        assert m.calidSheep();

        print "Clone_Via_Map world:", fmtobj(a),"\n";
print "VARIANT COW ", |(m'.oHeap - m'.ks)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";
        assert CallOK(m.oHeap);

        b := a;
        assert b.fieldModes == a.fieldModes;




        assert a !in m.ks;
        assert a in m.oHeap;
        assert m.oHeap !! m.ns by {
          reveal m.calidObjects();
          assert m.calidObjects();
          assert m.oHeap !! m.ns;
        }
        assert outside(a,m.o);
        a.CallMyOwnersWillWitherAway(a, m.oHeap);

        reveal m.calidObjects();
        assert m.calidObjects();
        assert m.ks <= m.oHeap; 
        OutsidersArentMapValues(a,m);

        reveal m.calidMap();
        assert m.calidMap();
        assert MapOK(m.m);
        assert (forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys);
        assert m.m.Keys == m.ks;
        assert (forall x <- m.ks :: x.owners() <= m.ks); 

        assert a !in m.vs;
        m := m.putOutside(a);   ///HOPEY?  CHANGEY?
        assert b.fieldModes == a.fieldModes;

                    assert (b == a) by {
              assert not(inside(a, m.o));   //glurk
              assert m.AreWeNotMen(a,m);
              assert b == a;      //double glurk 
            }
        
}









method {:isolate_assertions} Clone_Inside_Heap(a : Object, m' : Map)
      returns (b : Object, m : Map)
  decreases (m'.oHeap - m'.ks), a.AMFO, (a.fields.Keys), 15 //Clone_Inside_Heap

//this case
  requires a !in m'.ks
  requires inside(a,m'.o)
  requires a.region.Heap?

  requires a.extra == {} //extra not yet cloned


//all Clone_
  requires m'.calid()
  requires a in m'.oHeap 
  requires COK(a, m'.oHeap)
  
  //requires CallOK(a.extra,m'.oHeap); ///now covered by the above?

  ensures  m.calid()
  ensures  a in m.ks
  ensures  a in m.m.Keys
  ensures  b in m.vs
  ensures  b in m.m.Values
  ensures  b in m.ns
  ensures  a in m.m.Keys && m.at(a) == b
  ensures  COK(b, m.oHeap+m.ns)

//on reflection, none of these make sense - or perhaps this one does?
//  ensures  b.fields == map[]

//should I package this up - as aw twostate or a onestate?
//it;s about clonbamps, so clonmapLEQ or clonmapEXTENDS
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.ks >= m'.ks + {a}
  ensures  m.vs >= m'.vs + {b}
  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns >= m'.ns
//  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
//  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert 
  ensures MapOK(m.m) 
  ensures a.AMFO <= m.ks  //seems weird but we are populating m, right...
  ensures a.extra <= m.ks //ditto?
  //ensures b.AMFO == set x <- a.AMFO :: m.m[x] 

   ensures b.fieldModes == a.fieldModes
//   ensures b.fields.Keys == a.fields.Keys

   //modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
   //modifies (set o : Object)`fields
   modifies {}
   {
        m := m';

        assert COK(a, m.oHeap);
        assert m.calid();
        assert inside(a,m.o);

        assert ANKS: a !in m.ks;
        assert COKFOURWAYS: m.calid(); 

print "Clone_Inside_Heap owners:", fmtobj(a), " owned by ", fmtobj(a.region.owner) ,"\n";
print "VARIANT CIH ", |(m'.oHeap - m'.ks)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";
        assert COK(a.region.owner, m.oHeap) by {
            assert m.calid();
            reveal m.calid();
            assert m.calidOK();
            reveal m.calidOK();      
            COKfromCallOK(a, m.oHeap);
            assert COK(a, m.oHeap);
            reveal COK();
            assert a.Ready();
            assert a.region.owner in a.AMFO;            
            assert COK(m.o, m.oHeap);
            assert CallOK(m.oHeap);
            COKAMFO(a, m.oHeap);
            assert CallOK(a.AMFO, m.oHeap);
            assert a.region.owner in a.AMFO;
            COKfromCallOK(a.region.owner, m.oHeap);
            assert COK(a.region.owner, m.oHeap);

        }

//makde COK check for this, no need to do another level here?
// assert forall x <- a.extra :: COK(x,m.oHeap);
// forall x <- a.extra ensures COK(x,m.oHeap) 
// {
//   assert true;
// }   
//assert CallOK(a.extra,m.oHeap);

        assert (a.region.owner.AMFO < a.AMFO) by {
            assert m.calid();
            reveal m.calid();
            assert m.calidOK();
            reveal m.calidOK(); 
            COKfromCallOK(a, m.oHeap);
            assert COK(a, m.oHeap);
            reveal COK();
            assert a.Ready();
            assert a.AMFO > a.region.owner.AMFO;
            assert a.region.owner.AMFO <=  a.AMFO;
                    }


reveal COK(); assert a.region.owner.extra == {}; //extra not yet cloned

        var rowner, rm := Clone_Via_Map(a.region.owner, m);
        assert rm.from(m);

        assert COK(rowner, rm.oHeap+rm.ns);

        reveal rm.calid();
        reveal rm.calidObjects();
        reveal rm.calidOK();
        reveal rm.calidMap();
        reveal rm.calidSheep();
        assert rm.calid();
        assert rm.calidObjects();
        assert rm.calidOK();
        assert rm.calidMap();
        assert rm.calidSheep();

        assert COK(a.region.owner, rm.oHeap);
        assert CallOK(rm.oHeap);
        assert CallOK(rm.ks, rm.oHeap);
        assert CallOK(rm.vs, rm.oHeap+rm.ns);
        assert CallOK(rm.ns, rm.oHeap+rm.ns);



//should we rename oHeap as context?

        assert COK(rm.o, rm.oHeap);
        assert CallOK(rm.oHeap);

// COKAMFO(rowner, rm.oHeap+rm.ns);
// assert {rowner}+rowner.AMFO == rowner.AMFO+{rowner};
// assert CallOK({rowner}+rowner.AMFO,
// 
// assert CallOK({rowner}+rowner.AMFO, rm.oHeap+rm.ns);


assert CallOK(rm.oHeap); //ensured by clone
CallOKWiderContext(rm.oHeap,rm.oHeap,rm.ns);
assert CallOK(rm.oHeap,rm.oHeap+rm.ns);

assert CallOK(rm.ns, rm.oHeap+rm.ns);  //ensured by clone
CallOKWiderFocus(rm.oHeap, rm.ns, rm.oHeap+rm.ns);

assert CallOK(rm.oHeap+rm.ns);

assert COK(rowner, rm.oHeap+rm.ns);  //ensured by clone

///need this for later...
assert COK(rowner, rm.oHeap+rm.ns);
assert CallOK(rm.oHeap+rm.ns);


        if (a in rm.ks) {
            m := rm;
            b := rm.at(a);
            assert m.calid();
            assert CallOK(m.vs, m.oHeap+m.ns);
            assert b in m.m.Values; 
            assert m.m.Values == m.vs;
            assert b in m.vs;
            assert (b in m.ns) by 
               {
                reveal m.calid();
                assert m.calid() && m.calidObjects() && m.calidOK() && m.calidSheep();
                reveal m.calidSheep();
                reveal m.AreWeNotMen(); 
                assert forall x <- m.ks :: m.AreWeNotMen(x, m);
                assert b == m.m[a];
                assert a in m.ks;
                assert inside(a,m.o);
                assert m.m[a] in m.ns;
                assert b in m.ns;
               }
            assert b in m.ns;
            COKfromCallOK(b, m.vs, m.oHeap+m.ns);
            assert COK(b, m.oHeap+m.ns);

            assert b.fieldModes == a.fieldModes;
            assert m.calidSheep();

            assert m.ks >= m'.ks + {a};
            assert m.vs >= m'.vs + {b};

            return; 
        } // a in rm.ks - i.e. randomly done while cloning owners

assert COK(rowner, rm.oHeap+rm.ns);
assert CallOK(rm.oHeap+rm.ns);
assert a.extra <= rm.oHeap by { assert COK(a, rm.oHeap); reveal COK(); }
CallOKNarrowFocus({},rm.oHeap+rm.ns);    //WTF is this doiung?  why?
assert CallOK({},rm.oHeap+rm.ns);        //and this one?


      
        b := new Object.cake(a.fieldModes, rowner, rm.oHeap+rm.ns, "clone of " + a.nick);  // no extra

        // currently ignoring REXTRA //TODO...   //extra not yet cloned
        // var rextra := set x <- a.extra :: m.m[x];
        // b := new Object.cake(a.fieldModes, rowner, rm.oHeap+rm.ns, "clone of " + a.nick, rextra);

        assert fresh(b);
        assert b.fieldModes == a.fieldModes;

        assert b !in rm.oHeap;
        assert b !in rm.m.Values;
        assert a !in rm.m.Keys;
        assert COK(b, (rm.oHeap+rm.ns)+{b});
        // COKWiderContext(b, )
        // assert COK(b, {b} + rm.oHeap+rm.m.Values);
        assert a.region.Heap? == b.region.Heap?;

        reveal rm.calid();
        reveal rm.calidObjects();        
        reveal rm.calidOK();
        reveal rm.calidMap();
        reveal rm.calidSheep();   

        assert rm.calid();
        assert rm.calidObjects();
        assert rm.calidOK();
        assert rm.calidMap();
        assert rm.calidSheep();

        assert COK(a,rm.oHeap);
        reveal COK();
        assert a.owners() <= rm.oHeap;
        assert a !in rm.ks; // by { reveal ANKS; }
        assert b !in rm.vs;
        assert COK(b, rm.oHeap+rm.ns+{b});
        assert b !in (rm.oHeap+rm.ns);

        assert MapOK(rm.m);
        //assert forall kx <- a.extra :: rm.m[kx] in b.extra;   //extra not yet cloned

assert a.extra == {};
assert a.owners() <= rm.ks;


        var xm := rm.putInside(a,b);
        assert xm.m == MappingPlusOneKeyValue(rm.m,a,b);
        
assert xm.ks >= rm.ks + {a};
assert xm.vs >= rm.vs + {b};
        assert COK(b, xm.oHeap+xm.ns);  

        MapOKFromCalid(xm);
        assert xm.calid();

  
/////   /////    /////    /////   /////    /////    /////   /////    /////    
/////   preconditiosn for call of Clone_All_Fields
/////   /////    /////    /////   /////    /////    /////   /////    /////    


  assert xm.calid();
  assert COK(a, xm.oHeap);
  assert COK(b, xm.oHeap+xm.ns);
  assert b.fields.Keys == {};
  assert a.fields.Keys <= a.fieldModes.Keys;
  assert a.fieldModes == b.fieldModes;
  assert a in xm.oHeap  ;
  assert a in xm.ks;
  assert b in xm.vs;
  assert b in xm.ns;
  assert (a in xm.m.Keys) && xm.m[a] == b;
  assert xm.o    in xm.oHeap;
  assert xm.ks   <= xm.oHeap;
  assert a.region.Heap? == b.region.Heap?;

/////   /////    /////    /////   /////    /////    /////   /////    /////    
/////   /////    /////    /////   /////    /////    /////   /////    /////    

assert (m'.oHeap - m'.ks) >=  (xm.oHeap - xm.ks +{a});
assert old((a.fields.Keys)) >= (a.fields.Keys);
assert 15 >= 10;

//  (m'.oHeap - m'.ks), a.AMFO, (a.fields.Keys), 15 

// (m'.oHeap - m'.ks +{a}), a.AMFO, (a.fields.Keys), 10 

m := xm;
  //      m := Clone_All_Fields(a,b, xm);

//assert b.fields.Keys == a.fields.Keys;

assert m.ks >= xm.ks;
assert m.vs >= xm.vs;
  

assert m.ks >= m'.ks + {a};
assert m.vs >= m'.vs + {b};
  }



method Clone_Inside_World(a : Object, m' : Map)
      returns (b : Object, m : Map)
  decreases (m'.oHeap - m'.ks), a.AMFO, (a.fields.Keys), 15 //Clone_Inside_World(

//this case
  requires inside(a,m'.o)
  requires a.region.World?
  requires a !in m'.ks

  requires a.extra == {} //extra not yet cloned
  
//all Clone_
  requires m'.calid()
  requires a in m'.oHeap 
  requires COK(a, m'.oHeap)


  ensures  m.calid()
  ensures  a in m.ks
  ensures  a in m.m.Keys
  ensures  b in m.vs
  ensures  b in m.m.Values
  ensures  b in m.ns
  ensures  a in m.m.Keys && m.at(a) == b
  ensures  COK(b, m.oHeap+m.ns)

  ensures  b.fields.Keys == a.fields.Keys

  // ensures fresh(b)

//should I package this up - as aw twostate or a onestate?
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.ks >= m'.ks + {a}
  ensures  m.vs >= m'.vs + {b}
  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns >= m'.ns
//  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
//  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert 
  ensures MapOK(m.m) 
  ensures a.AMFO <= m.ks  //seems weird but we are populating m, right...
  ensures a.extra <= m.ks //ditto?
  //ensures b.AMFO == set x <- a.AMFO :: m.m[x] 


   ensures b.fieldModes == a.fieldModes
//   ensures b.fields.Keys == a.fields.Keys
   modifies {}
  {
        m := m';

//  assert  m.ks >= m'.ks + {a};
//  assert  m.vs >= m'.vs + {b};

print "VARIANT CIW ", |(m'.oHeap - m'.ks)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";

        assert COK(a, m.oHeap);
        assert m.calid();
        assert inside(a,m.o);

        assert ANKS: a !in m.ks;
        assert COKFOURWAYS: m.calid(); 


        reveal m.calid();
        assert m.calid();
        reveal m.calidOK();
        assert m.calidOK();

        print "Clone_Via_Map world:", fmtobj(a),"\n";

        assert CallOK(m.oHeap);   

        assert BEFORE: m.calid(); 
    
        b := new Object.frozen2(a.fieldModes, m.oHeap);

        b.nick := "clone of " + a.nick; 

        assert fresh@BEFORE(b);
        assert b !in m.oHeap;
        assert b !in m.ns;
        assert unchanged@BEFORE(m.oHeap`fields, m.oHeap`fieldModes);
        assert unchanged@BEFORE(m.ns`fields, m.ns`fieldModes);

        assert m.calid();

        assert fresh(b);
        assert b !in m.oHeap + m.ns;
        assert COK(a, m.oHeap); // by { reveal COKSTART; }
        assert COK(b, m.oHeap+{b});
        COKWiderContext(b, m.oHeap+{b}, m.ns);
        assert (m.oHeap+{b})+m.ns == m.oHeap+m.ns+{b};
        assert COK(b, m.oHeap+m.ns+{b});
   
        assert a !in m.ks by { reveal ANKS; }  //was m.m.Keys...
        assert a !in m.m.Keys by { reveal ANKS;  reveal m.calid(); assert m.calid(); reveal m.calidObjects(); assert m.calidObjects(); }  //was m.m.Keys...

        RVfromCOK(a, m.oHeap);
        var mx := m.putInside(a,b);  

        assert (mx.ks == mx.m.Keys && mx.vs == mx.m.Values) 
        by {
          reveal m.putInside();
          assert mx.calid(); reveal mx.calid();
          assert mx.calidObjects(); reveal mx.calidObjects();
        }
        assert mx.m == m.m[a:=b];
        assert mx.m == MappingPlusOneKeyValue(m.m,a,b);

        assert  mx.ks >= m'.ks + {a};
        assert  mx.vs >= m'.vs + {b};

        assert COK(b, mx.oHeap+mx.ns);

        reveal mx.calidMap();
        assert mx.calid();
        reveal mx.calidMap();
        assert mx.calidMap();
        assert MapOK(mx.m);

        assert a.AMFO == {a};
        assert a.AMFO <= mx.ks;

        m := Clone_All_Fields(a,b, mx);

        assert  (m.ks >= mx.ks && m.vs >= mx.vs)
        by {
        assert m.calid();
        reveal m.calid(); 
        assert m.calidObjects();
        reveal m.calidObjects();
        }

        assert  m.ks >= m'.ks + {a};
        assert  m.vs >= m'.vs + {b};

  }




















method Clone_Field_Map(a : Object, n : string, b : Object, m' : Map)
   returns (m : Map)
//clone field a.n into b.n
//a should be preexisting (in m'.oHeapl); b should be "new"  in m'.ns

  decreases (m'.oHeap - m'.ks +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5 //Clone_Field_Map

  requires m'.calid()
  requires COK(a, m'.oHeap)
  requires COK(b, m'.oHeap+m'.ns)

  requires n  in a.fields.Keys
  requires n !in b.fields.Keys

  requires n  in a.fieldModes
  requires n  in b.fieldModes
  requires a.fieldModes == b.fieldModes
  requires FLDMODZ: a.fieldModes == b.fieldModes

 
  requires a in m'.oHeap  
  requires a in m'.ks

  requires b in m'.vs
  requires b in m'.ns
  requires (a in m'.m.Keys) && m'.m[a] == b
  requires m'.o    in m'.oHeap
  requires m'.ks   <= m'.oHeap

  requires b.fieldModes == a.fieldModes

  // requires b.fieldModes[n] == Evil //evilKJX this is actually evil 
                                   //well not *that* evil as I still must satisfy refOK
   
  requires forall n <- b.fields :: (n in b.fieldModes) &&
              AssignmentCompatible(b, b.fieldModes[n], b.fields[n])

  //consequently
  requires refOK(a, a.fields[n])
  requires a.region.Heap? == b.region.Heap?


    
  ensures  b.fields.Keys == old(b.fields.Keys) + {n}
  ensures  (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys - b.fields.Keys)
  ensures  m.calid()

  ensures  a in m.ks
  ensures  (a in m.m.Keys) && m.m[a] == b

  ensures  n in b.fields
  ensures  (a.fields[n] in m.m.Keys) && m.m[a.fields[n]] == b.fields[n]

  ensures  b in m.vs

  ensures  mapLEQ(m'.m,m.m)
  
  ensures  CallOK(m.oHeap)
  ensures  COK(a, m.oHeap)
  ensures  COK(b, m.oHeap+m.ns)
  ensures  CallOK(m.vs, m.oHeap+m.ns)
  ensures  CallOK(m.ns, m.oHeap+m.ns)

  ensures  m.o     == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns    >= m'.ns
  ensures  m.ks    >= m'.ks
  ensures  m.vs    >= m'.vs
  ensures  m.ks    <= m.oHeap 

  ensures a.fieldModes == b.fieldModes

  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap)
//  ensures unchanged(m.vs - {b}) //duesb;t veruft....

//  modifies (set o : Object | o !in m'.oHeap)`fields
// modifies (set o : Object | o !in ((m'.oHeap+m'.ns) - {b}))`fields
  //or can this  be modifies m'.ns? 
  modifies b`fields   ///GGRRR
  {

  m := m';

  var v_cfm := ((m.oHeap - m.ks +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Clone_Field_Map




 print "VARIANT CFM ", |(m'.oHeap - m'.ks)+{a}|, " ", |a.AMFO|, " ", |(a.fields.Keys - b.fields.Keys - {n})|, " ", 10, "\n";

 var onb := m.ns - {b};
 var ctx := (m.oHeap+m.ns);

    assert CallOK(onb, ctx) by
       {
        assert m.calid(); reveal m.calid(); reveal m.calidOK();
        assert CallOK(m.ns, m.oHeap+m.ns);
        CallOKNarrowFocus(onb, m.ns, m.oHeap+m.ns);
        assert CallOK(onb, m.oHeap+m.ns);
      }

    assert CallOK(m.oHeap) by {
      assert m.calid(); reveal m.calid();
      assert m.calidOK(); reveal m.calidOK();
      assert CallOK(m.oHeap);
    }

assert m.calid();

    var ofv := COKat(a,n,m.oHeap);

label B3:
assert m.calid();

reveal COK(); assert ofv.extra == {}; //extra not yet cloned

    var rfv, rm := Clone_Via_Map(ofv, m);

assert unchanged@B3(m.oHeap);

    assert rfv in  rm.oHeap+rm.vs;
    assert rfv in  rm.oHeap+rm.ns;
    assert COK(rfv,rm.oHeap+rm.ns);
    assert refOK(b, rfv);
    assert AssignmentCompatible(b, b.fieldModes[n], rfv) 
    by {
// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

  assert b.fieldModes[n] == a.fieldModes[n];

 assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]) by
  {
      reveal COK();
      assert COK(a, m.oHeap);
      assert a.Valid();
      assert a.AllFieldsContentsConsistentWithTheirDeclaration();
      assert forall n <- a.fields.Keys :: AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
      assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
  }

  



  match (b.fieldModes[n]) {
    case Evil => 
     assert b.fieldModes[n] == Evil;
     EVILisCompatibleWithAnything(b,rfv);
     assert AssignmentCompatible(b, b.fieldModes[n], rfv);

    case Rep | Owned(_) | Loaned(_) => 
        assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
        assert ofv == a.fields[n];
        assert ofv.region.Heap?;
        assert ofv.region.owner == a;
        assert rfv.region.Heap?;
        assert b == rm.m[a];
        assert rfv == rm.m[ofv];
        assert b == rfv.region.owner;
        assert b == rm.m[a.fields[n].region.owner];
        assert b == rfv.region.owner;
        assert AssignmentCompatible(b, b.fieldModes[n], rfv);

    case Peer =>
        assert AssignmentCompatible(a, a.fieldModes[n], ofv);
        assert a.region == ofv.region;
        if a.region.Heap? {
          assert b.region.Heap?;
          assert rm.m[a.region.owner] == b.region.owner;
          assert rm.m[ofv.region.owner] == rfv.region.owner;
          assert rfv.region.owner == b.region.owner;
          assert b.region.owner       == rfv.region.owner;
        } else {    
              assert AssignmentCompatible(a, a.fieldModes[n], rfv);

          assert a.region.World?;
          assert b.region.World?;
        }
        assert b.region == rfv.region;
        assert AssignmentCompatible(b, b.fieldModes[n], rfv);

    case Borrow(pp,bb,nn,ff) => 
        assert refOK(a,a.fields[n]);
        assert refOK(b,rfv);
        assert AssignmentCompatible(b, b.fieldModes[n], rfv);
     }



// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
    }




assert rm.calid();
assert m.calid();
    m := rm;
assert rm.calid();
assert m.calid();

bNotInoHeap(b,m);

label B4:

assert m.calidOK() by { reveal m.calid(); }
     
  assert COK(b, rm.oHeap+rm.ns) by
  {
    assert b in m'.ns;
    assert b in m.ns;
    assert b in rm.ns;
    assert COK(b, m'.oHeap+m'.ns);
    assert m'.ns <= rm.ns <= m.ns;
    COKWiderContext2(b,m'.oHeap+m'.ns,rm.oHeap+rm.ns);
    assert COK(b, rm.oHeap+rm.ns);
  }


  assert 
     && CallOK(m.vs, m.oHeap+m.ns) 
     && CallOK(m.ns, m.oHeap+m.ns) 
     && ( m.ks    <= m.oHeap )
        by { reveal m.calid(); reveal m.calidOK(); }

CallOKNarrowFocus(m.vs-{b}, m.vs, m.oHeap+m.ns);
CallOKNarrowFocus(m.ns-{b}, m.ns, m.oHeap+m.ns);

  assert CallOK(m.vs-{b}, m.oHeap+m.ns);
  assert CallOK(m.ns-{b}, m.oHeap+m.ns);

  assert b in m.ns;

    b.fields := b.fields[n := rfv]; 


  assert CallOK(m.vs-{b}, m.oHeap+m.ns);
  assert CallOK(m.ns-{b}, m.oHeap+m.ns);



  assert m.m[ofv] == rfv;
  assert rfv in m.vs;
  assert rfv in m.oHeap+m.ns;


if (b != rfv) {

  assert COK(rfv,m.oHeap+m.ns); 
  assert COK(b,  m.oHeap+m.ns) by {
    reveal COK();
      assert refOK(b, rfv);
  assert AssignmentCompatible(b, b.fieldModes[n], rfv);

    assert COK(b,  m.oHeap+m.ns);

  }

} else {
  assert b == rfv;// gulp!

  assert COK(b,  m.oHeap+m.ns) by {
    reveal COK();
    assert refOK(b, rfv);
    assert AssignmentCompatible(b, b.fieldModes[n], rfv);
    assert COK(b,  m.oHeap+m.ns);
}
  assert COK(rfv,m.oHeap+m.ns); 
}


assert COK(b, m.oHeap+m.ns) &&  COK(rfv,m.oHeap+m.ns); 

assert   (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys - b.fields.Keys) by {
  assert a.fields.Keys == old(a.fields.Keys);
  assert b.fields.Keys == old(b.fields.Keys)+{n};
}


assert 
  && CallOK(m.vs, m.oHeap+m.ns) 
  && CallOK(m.ns, m.oHeap+m.ns) 
by {
  assert CallOK(m.vs-{b}, m.oHeap+m.ns); //OK
  assert CallOK(m.ns-{b}, m.oHeap+m.ns);

  assert COK(b, m.oHeap+m.ns);
  assert b in  m.oHeap+m.ns by { reveal COK(); }
  CallOKfromCOK(b, m.oHeap+m.ns);
  CallOKWiderFocus(m.ns-{b}, {b}, m.oHeap+m.ns);
  assert (m.ns-{b} + {b}) == m.ns;

  assert b in m'.vs;
  assert b in  m.vs;

  assert m.vs <= m.oHeap+m.ns by { reveal m.calid(); reveal m.calidOK(); }

  assert COK(b, m.oHeap+m.ns);
  assert b in  m.oHeap+m.ns by { reveal COK(); }
  CallOKfromCOK(b, m.oHeap+m.ns);
  CallOKWiderFocus(m.vs-{b}, {b}, m.oHeap+m.ns);
  assert (m.vs-{b} + {b}) == m.vs;


  assert CallOK(m.vs, m.oHeap+m.ns);
  assert CallOK(m.ns, m.oHeap+m.ns);
}



assert  m.calidOK()
by {
  assert old@B4(rm.calidOK());
  reveal m.calidOK();

assert old@B4(CallOK(m.vs, m.oHeap+m.ns));
assert old@B4(CallOK(m.ns, m.oHeap+m.ns));


  assert rfv in rm.vs;
  assert rfv in rm.oHeap+rm.ns;
  assert COK(rfv,m.oHeap+m.ns); 

  assert (m.o in  m.oHeap);
  assert (m.ks <= m.oHeap);
  assert (m.vs <= m.oHeap+m.ns);
  assert COK(m.o, m.oHeap);
  assert CallOK(m.oHeap);
  assert CallOK(m.ks, m.oHeap);

  assert COK(b,m.oHeap+m.ns);

  // assert CallOK(m.vs, m.oHeap+m.ns);
  // assert CallOK(m.ns, m.oHeap+m.ns);
  assert m.calidOK();
}



  assert m.calid() by 
    {
      reveal m.calid();
      reveal m.calidObjects();
      reveal m.calidOK();
      reveal m.calidMap();
      reveal m.calidSheep();      

      assert m.calidObjects();
      assert m.calidOK();
      assert m.calidMap();

      assert m.ks == m.m.Keys;
      reveal m.AreWeNotMen(); 
      assert forall x <- m.ks :: m.AreWeNotMen(x, m);
      assert m.calidSheep();

      assert m.calid();

    }
} //end Clone: /_Field_Map

function mapThruMap(os: set<Object>, m : Map) : set<Object>
  reads m.oHeap`fields, m.oHeap`fieldModes
  reads m.ns`fields, m.ns`fieldModes      
  requires m.calid()
  requires os <= m.ks
  requires os <= m.m.Keys
{
  reveal m.calid();
  set o <- os :: m.m[o]
}



// method Clone_Extra_Owners(a : Object,  m' : Map)  returns (m : Map) 
//    
//   decreases (m'.oHeap - m'.ks), a.AMFO, (a.fields.Keys), 12
// 
//   requires a.extra == {} //extra not yet cloned
// 
//   requires m'.calid()
//   requires a !in m'.ks     //can we just reply on clone to do the RIGHT THING
//   requires a in m'.oHeap 
//   requires COK(a, m'.oHeap)
// 
//   // ensures  m.calid()
//   // ensures  a.extra <= m.ks
//   // ensures  a.extra <= m.m.Keys
//   // ensures  && (a.extra <= m.ks)
//   //          && (a.extra <= m.m.Keys)
//   //          && mapThruMap(a.extra, m) <= m.vs
// {
//         var rm := m';
//         var b : Object; 
// 
// 
// 
//         assert a !in rm.ks;
//         assert a !in rm.vs by { 
//           
//           
//     //            assert not(inside(a,rm.o));
//     //            assert a !in rm.m.Keys;
//                 assert rm.calid(); 
//                 rm.WeAreDevo();
//                 assert forall k <- rm.m.Keys :: rm.AreWeNotMen(k,rm);
//                 assert a  in rm.oHeap;
//                 assert a !in rm.ns;
//           
//           
//           
//           Map.AintNoSunshine(a, rm);
//           assert a !in rm.vs; }
//         assert rm.ks >= m'.ks;
//         assert mapLEQ(m'.m,rm.m);
//         assert rm.from(m');
// 
// //    //maintaing MapOK
// //         assert AMFOOKRM: a.owners() <= rm.ks by {
// //             reveal rm.calid();
// //             assert rm.calid();
// //             reveal rm.calidMap();
// //             assert rm.calidMap();
// //             assert MapOK(rm.m);
// //             reveal rm.calidObjects();
// //             assert rm.calidObjects();             
// //             assert (forall x <- rm.ks, oo <- x.AMFO :: oo in rm.ks);
// //             assert a.owners() <= rm.ks by {
// //                reveal COK(); 
// //                assert COK(a,m.oHeap); 
// //                assert a.AMFO <= m.oHeap;
// // //               assert a.owners() <= rm.ks;
// //                }
// //         }
// 
// 
// 
//         assert a in rm.oHeap; 
//         assert COK(a, rm.oHeap);
//         reveal COK();
//         assert a.AMFO <= rm.oHeap;
//       //  assert a.owners() <= rm.ks;
//       if (outside(a,rm.o)) {
//         OutsidersArentMapValues(a,rm);
//         assert a !in rm.vs;
//         assert a !in rm.ks;
//         assert not(inside(a, rm.o)); 
//       }
// 
//         //m := rm[a:=b];     
// 
// 
//         assert COK(a, rm.oHeap);
// 
//         assert rm.calid();
//         assert a in rm.oHeap;
//         assert COK(a, rm.oHeap);
//         assert a.extra <= rm.oHeap; 
// 
//         assert CallOK(rm.oHeap) by {
//           reveal rm.calid(), rm.calidOK();
//           assert rm.calid();
//           assert rm.calidOK();
//           reveal CallOK(), COK();
//           assert CallOK(rm.oHeap);
//         }
// 
// 
//         var xm := rm;
//         assert xm.ks >= m'.ks;
//         assert mapLEQ(m'.m,xm.m);    
//         assert xm.from(rm);
//         assert xm.from(m');
// 
//         assert a !in xm.ks;
//         assert a !in xm.vs;
// 
// 
//         var MX := a.extra - xm.ks;
//         assert MX <= a.extra;
//         var xo : Object;
//         var rr : Object;
//         var oldmks  : set<Object>;  //dont fucking ask
//         var oldmok :=  false;
// 
//         assert !oldmok;
//         assert xm == rm;
//         assert xm.ks >= (m'.ks);
//         assert mapLEQ(m'.m,xm.m);    
//         assert xm.from(m');
// 
//         assert a !in xm.ks;
// 
//         while ((MX != {}) && (a !in xm.ks))
//           decreases MX
//           invariant MX == a.extra - xm.ks
//           invariant MX <= a.extra
//           invariant xm == rm
//           invariant xm.calid()
//           invariant rm.calid()
//           invariant m'.calid()
//           invariant xm.from(m')  
//           invariant MX <= xm.oHeap            
//           invariant CallOK(xm.oHeap)    
//           invariant a.AMFO - {a} <= xm.ks + MX
//           invariant a.extra <= a.AMFO
//           invariant oldmok ==> assigned(oldmks)
//           invariant oldmok ==> (xm.ks > oldmks)
//           invariant m'.oHeap == xm.oHeap
//           invariant oldmok ==> ((m'.oHeap - oldmks) > (xm.oHeap - xm.ks))
//           invariant xm.ks >= (m'.ks)
//           invariant xm.vs >= (m'.vs)
//           invariant a !in xm.ks
//         {
//           assert xm == rm;
//           xo :| xo in MX;
//           assert xo in MX;
//           MX := MX - {xo};
//            
//           assert xm.calid();
//           assert xo in xm.oHeap;
//           COKfromCallOK(xo,xm.oHeap);
//           assert COK(xo,xm.oHeap);
//           assert xo !in xm.ks;
//         
//         
//           assert oldmok ==> (m'.oHeap - oldmks) > (xm.oHeap - xm.ks);
// 
// assert xo in a.AMFO;
// assert a.Ready();
// assert xo in a.extra;
// assert a.AMFO > xo.AMFO;
// 
// 
//           assert (m'.oHeap) == m'.oHeap == xm.oHeap;
//           assert xm.ks >= (m'.ks);
//           assert xm.from(m');
// 
//   assert  mapLEQ(m'.m,xm.m) by 
//                { reveal xm.calid(); assert xm.calid();
//                  reveal xm.calidObjects(); assert xm.calidObjects();
//                  assert m'.ks <= xm.ks;
//                  assert m'.vs <= xm.vs; 
//                  assert m'.ks == m'.m.Keys;
//                  assert m'.vs == m'.m.Values;       
//                  assert xm.ks == xm.m.Keys;
//                  assert xm.vs == xm.m.Values;                              
//                  assert m'.m.Keys <= xm.m.Keys;
//                  assert m'.m.Values <= xm.m.Values;
//                  assert forall k <- m'.m.Keys :: k in xm.m.Keys;
//       assert forall k <- m'.m.Keys :: k in xm.m.Keys && (m'.m[k] == xm.m[k]);
//                 }
//         
// 
//                   assert xm.ks >= m'.ks;
//                 assert a !in xm.ks;          
// 
//           assert ((m'.oHeap - m'.ks)) >= (xm.oHeap - xm.ks);
// 
// assert  ((a.AMFO)
//   decreases to
//         (xo.AMFO));
//       
//         assert ((m'.oHeap - m'.ks), 
//                (a.AMFO),
//                (a.fields.Keys), 
//                (15) 
//           decreases to 
//                xm.oHeap - xm.ks, 
//                xo.AMFO, 
//                xo.fields.Keys, 
//                20);
// 
//       
//           rr, rm := Clone_Via_Map(xo, xm);
//           assert rm.ks >= m'.ks;
//           assert mapLEQ(m'.m,rm.m);    
//           assert rm.from(m');
// 
//       if (a in rm.ks) { 
//                 m := rm;
//                 assert m.calidObjects() by {  reveal m.calid(); assert  m.calid();  }
//                 assert  a in m.ks by { reveal m.calidObjects(); assert m.calidObjects(); }
//                 assert  a in m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
//                 b := m.m[a];
//                 //
// 
//                 assert  b in m.vs by { reveal m.calidObjects(); assert m.calidObjects();  assert b in m.m.Values; }
//                 assert  b in m.m.Values by { reveal m.calidObjects(); assert m.calidObjects(); }
//                 assert m.calidOK() by {  reveal m.calid(); assert  m.calid();  }
//                 assert  a in m.m.Keys && m.at(a) == b; 
//                 assert  COK(b, m.oHeap+m.ns) by {
//                 assert b in m.vs;
//                 assert CallOK(m.vs, m.oHeap+m.ns) by { reveal m.calidOK(); }
//                 COKfromCallOK(b, m.vs, m.oHeap+m.ns);   }
// 
//                 assert m.from(m');
// 
//                 assert  mapLEQ(m'.m,m.m) by 
//                         { reveal m.calidObjects(); assert m.calidObjects();
//                           assert m'.ks <= m.ks;
//                           assert mapLEQ(m'.m,m.m);    
//                           assert m'.m.Keys <= m.m.Keys;
//                           assert m'.m.Values <= m.m.Values;
//                           }
//                 assert  m.ks >= m'.ks + {a} by { reveal m.calidObjects(); assert m.calidObjects(); }
//                 assert  m.vs >= m'.vs + {b} by { reveal m.calidObjects(); assert m.calidObjects(); }
//                 assert  m.o == m'.o;
//                 assert  m.oHeap == m'.oHeap;
//                 assert  m.ns >= m'.ns;
//                 assert MapOK(m.m);
//                 assert forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys;
//                 assert  a in m.m.Keys;
//                 assert forall oo <- a.AMFO :: oo in m.m.Keys;
//                 assert a.AMFO <= m.m.Keys;
//                 assert m.ks == m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
//                 assert a.AMFO <= m.ks;
//                 assert a.extra <= m.ks;
// 
// 
//             
//                 assert  a == b by {
//                       reveal m.calid();
//                       assert m.calidMap();
//                       reveal m.calidMap();
//                   //    assert (forall x <- m.ks :: (not(inside(x,m.o)) ==> (m.m[x] == x)));
//                       assert not(inside(a,m.o));
//                       assert m.m[a] == a;
//                       assert a == b;
//                   }
// 
//              assert (b.fieldModes == a.fieldModes) by { assert a == b; }
//                       
//               return; 
//       }  // if a is in ks after clone -- if it got added magically...
// 
//           assert xo in rm.ks;
//           assert xm != rm;
//       //    assert rr == xo;
// 
//           MX := MX - rm.ks;
//           assert rm.ks > xm.ks;
//           oldmks := xm.ks;
//           oldmok := true;
//           xm := rm;
//           assert xm.ks >= m'.ks;       
//           assert xm.ks > oldmks;
// 
//           assert xm.from(m');
// 
// 
// //          MX := a.extra - rm.ks;          
//           assert xm == rm;
//         } // end loop MX
// 
// }
// 
// 








lemma MapOKFromCalid(m : Map) 
   requires m.calid()
   ensures  MapOK(m.m)
{  
  reveal m.calid();
  reveal m.calidMap();
}    

 

lemma  OutsidersArentMapValues(a : Object, m : Map)
  requires m.calid()
  requires a in m.oHeap  //technically redundant
  requires COK(a, m.oHeap)
  requires outside(a,m.o) //TEMP TO WRITEOUTSIDE CASE
  requires a !in m.ks
  ensures  a !in m.vs
{
  reveal m.calid();
  reveal m.calidObjects();
  assert m.calidObjects();
  reveal m.calidSheep();
  assert m.calidSheep();
  reveal m.AreWeNotMen(); 

  assert m.ns !! m.oHeap;
  assert forall x <- m.ks :: m.AreWeNotMen(x, m);

  assert 
        && (forall x <- m.ks :: (not(inside(x,m.o)) ==> (m.m[x] == x)))
        && (forall x <- m.ks ::    ((inside(x,m.o)) ==> (m.m[x] in m.ns)))
        ;

  if (a in m.vs) {
    AValueNeedsAKey(a,m.m);
    
    assert {:contradiction} not(outside(a,m.o));
    assert {:contradiction} false;
  }
}




lemma {:onlyClone} OwnersValidFromCalid(a : Object, m : Map)
    requires m.calid()
    requires 
      || COK(a, m.oHeap)
      || (CallOK(m.oHeap) && (a in m.oHeap))
      || (CallOK(m.ks, m.oHeap) && (a in m.ks))
      || (CallOK(m.ks, m.oHeap+m.ns) && (a in m.ks))
      || (CallOK(m.ks, m.oHeap+m.ns) && (a in m.ks))
    ensures a.Ready()
    ensures a.OwnersValid()
{
    reveal m.calid();
    assert m.calid();
    reveal m.calidOK();
    reveal COK();
    reveal CallOK();
    assert
      || (COK(a, m.oHeap) && a.Ready())
      || (CallOK(m.oHeap) && (a in m.oHeap) && a.Ready())
      || (CallOK(m.ks, m.oHeap) && (a in m.ks) && a.Ready())
      || (CallOK(m.ks, m.oHeap+m.ns) && (a in m.ks) && a.Ready())
      || (CallOK(m.ks, m.oHeap+m.ns) && (a in m.ks) && a.Ready());

    assert a.Ready();
    assert a.OwnersValid();
}
















///aux lemmas etc 

lemma  bNotInoHeap(b : Object, m : Map) 
// auxilliary lemma that says ensures that b is not in oHeap :-)
  requires b in m.ns
  requires m.calid()
  ensures  b in (set o : Object | o !in m.oHeap) 
{
  
  assert b in (set o : Object | o !in m.oHeap) by {
    assert m.calid(); reveal m.calid(); 
    assert m.calidObjects(); reveal m.calidObjects();
    assert m.ns !! m.oHeap; 
    assert b  in m.ns;                
    assert b !in m.oHeap;
    assert b  in (set o : Object | o !in m.oHeap);
}
}


predicate {:onlyfans} isIsomorphicMappingOWNED(a : Object, o : Object, m : Mapping, os : set<Object>)
//is a a clone of o via m within os
  decreases os
  reads os + m.Keys + m.Values
{
 && (a in m)  && (
  || (a == m[a])   //make it  easy on ourselves?
  || (
//   && ({a,o} <= os)
   && (a in m) 
   && (
      var b := m[a];
      && (b in os)
      && (|| (a.region.World? && b.region.World?) 
          || (&& (a.region.Heap? && b.region.Heap?)
              && isIsomorphicMappingOWNED(a.region.owner, b.region.owner, m, os - {a,b})) 
      )
      && forall n <- a.fields.Keys :: (
            && (a.fields[n] in m)
            && (n in b.fields)
            && (b.fields[n] == m[a.fields[n]]) 
            && (isIsomorphicMappingOWNED(a.fields[n], o, m, os - {a,b}))
         ) 
      )
   ) 
 )  
} 












