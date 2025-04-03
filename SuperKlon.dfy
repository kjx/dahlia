//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]


function  OOOLDEklonKV(c' : Klon, k : Object, v : Object) : (m : Klon)
  requires k !in c'.m.Keys
  requires v !in c'.m.Values
  requires klonCanKV(c', k, v)

reads k`fields, k`fieldModes
reads v`fields, v`fieldModes
reads c'.oHeap`fields, c'.oHeap`fieldModes
reads c'.ns`fields, c'.ns`fieldModes
// reads c'.o`fields, c'.o`fieldModes

reads c'.m.Values`fieldModes
reads c'.m.Keys`fieldModes
{
  klonKV(c', k, v)
}

function OOOLDEmapThruKlon(os: set<Object>, m : Klon) : (r : set<Object>)
  //image of os under klon mapping m
  // reads m.m.Keys`fields, m.m.Keys`fieldModes
  // reads m.m.Values`fields, m.m.Values`fieldModes
  requires os <= m.m.Keys
{ set o <- os :: m.m[o] }


//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//somwhere need series of "states"  pr "steps" pr "lemmata" of the Klon state
//1. created
//2. all owners of o in m.Keys  (Klown)
//3. ??>
//4. all owners & all fields of o in m.Keys ==> NEARLY DONE
//5. all o (and thus owners & all fields of o) in m.Keyes ==> DONE
//
// key preconditions
// all an object's owners are added before the object itself is added
// an object is added before its fields are added:
// ...BUT we never RETURN from a meethod that creates an object
//  UNTIL that object is fully populatioend with FIELDS

// function   mapThruKlown(k : Object, m : Klon) : Owner
//   requires k in m.m.Keys
//   // requires v in m.m.Values
//   // requires m.m[k] == v
//   requires m.readyAll()   //IN-KLON
//   requires k.owner <= m.m.Keys   //IN-KLON
//   requires k.AMFO  <= m.m.Keys   //IN-KLON
//   reads m.oHeap`fields,  m.oHeap`fieldModes
//   reads m.ns`fields, m.ns`fieldModes
// {
//   mapThruKlown(k.AMFO, m)
// }

function OLDmapThruKlown(k : set<Object>, m : Klon) : set<Object>
//note that this OLD version now looks at amfx not amfo
  requires m.readyAll()
  requires k <= m.m.Keys
{
  var CXTRA := m.c_amfx - mapThruKlon(m.o_amfx, m);
  var OXTRA := mapThruKlon(m.o_amfx, m) - m.c_amfx;

//  assert  (mapThruKlon(m.o_amfo, m) - OXTRA + CXTRA) == m.c_amfx;

  (mapThruKlon(k,m) - OXTRA + CXTRA )
}

function mapThruKlown(k : set<Object>, m : Klon) : set<Object>
  requires k <= m.m.Keys
  requires m.readyAll()
    { mapThruKlon(k,m) - m.oxtra + m.cxtra }



lemma LEMMAmapThruKlown(k : Owner, m : Klon)
  requires m.readyAll()   //IN-KLON
  requires k <= m.m.Keys
{
  var CXTRA := m.c_amfx - mapThruKlon(m.o_amfx, m);
  var OXTRA := mapThruKlon(m.o_amfx, m) - m.c_amfx;

  assert  (mapThruKlon(m.o_amfx, m) - OXTRA + CXTRA) == m.c_amfx;
}
//
// lemma MAP_AMFO_THRU_KLON_IS_NOOP(k : Object, m : Klon, r : set<Object>)
//   requires m.readyAll()
//   requires r == mapThruKlon(m.o_amfo, m) //should ben AMFX innit
//   requires m.calid()
//
//   // ensures  r == m.o_amfo
//   {
//   reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
//
//    assert forall x <- m.o_amfo :: (x == m.o) != not(inside(x, m.o));
//    assert forall x <- m.o_amfo ::  m.m[x] == x;
//
//
//   }


lemma MapThruIdentityKlon(o : Owner, m : Klon)
  requires o <= m.m.Keys
  requires forall x <- m.m.Keys :: m.m[x] == x
  ensures mapThruKlon(o, m) == o
  {}

///  MAPPED - (MTKA - CX)  + (CX - MTKA)


lemma KLUCKO(o : Object, m : Klon)
   requires m.readyOK(o)
   ensures  o.Ready()
   ensures  o in m.m.Keys
   ensures  o.owner <= m.m.Keys
   ensures  o.AMFO  <= m.m.Keys
{}

// predicate objectOwnerAttributesMapOK(o : Object, m : Klon)
// //nicer? version of mappingOwnersThruKlownOK?
// //do all o's owner attribute map to m.m[o]'s attributes
// //not currently needed?
//   requires m.readyAll()   //KLON-OK
//   requires m.m.Keys >= o.ntrnl > o.owner >= o.bound  //IN-KLON
//   requires m.m.Keys >= o.AMFO  > o.AMFX  >= o.AMFB   //IN-KLON
//   requires o in m.m.Keys  //IN-KLON
  // reads m.oHeap`fields, m.oHeap`fieldModes
  // reads m.ns`fields, m.ns`fieldModes
// {
//   var c := m.m[o];
//
//   && (c.bound == mapThruKlown(o.bound, m))
//   && (c.AMFB  == mapThruKlown(o.AMFB,  m))
//   && (c.owner == mapThruKlown(o.owner, m))
//   && (c.AMFX  == mapThruKlown(o.AMFX , m))
//   && (c.ntrnl == mapThruKlown(o.ntrnl, m))
//   && (c.AMFO  == mapThruKlown(o.AMFO,  m))  ///KJX HUMM
// }


predicate canMapOwnersThruKlown(o : Object, m : Klon)
 //predicate collecting preconditions to call mappingOwnersThruKlownOK. Don't ask.
{
  && m.m.Keys >= o.ntrnl > o.owner >= o.bound  //IN-KLON
  && m.m.Keys >= o.AMFO  > o.AMFX  >= o.AMFB   //IN-KLON
  && m.readyAll()   //KLON-OK
  && o in m.m.Keys //IN-KLON
  && m.ownersInKlown(o)
}

predicate {:isolate_assertions} mappingOwnersThruKlownOK(o : Object, m : Klon)
//do all o's owner attributes map through m?
//kjx: don't really need that v parameter do we?
//kjx: see allMapOwnersThruKlownOK for why k & v must be in m already

  // requires m.readyAll()   //KLON-OK
   requires m.m.Keys >= o.ntrnl > o.owner >= o.bound  //IN-KLON
   requires m.m.Keys >= o.AMFO  > o.AMFX  >= o.AMFB   //IN-KLON
  // requires o in m.m.Keys  //IN-KLON

  requires m.readyAll()   //KLON-OK
  requires o in m.m.Keys
  requires m.ownersInKlown(o)
//   requires m.readyOK(o)
// //  requires (KLUCKO(o,m); o.Ready())//BUGGY!
//   requires o.Ready()
//   requires m.m.Keys >= o.bound
//   requires m.m.Keys >= o.ntrnl > o.owner >= o.bound  //IN-KLON
//   requires m.m.Keys >= o.AMFO  > o.AMFX  >= o.AMFB   //IN-KLON
//   requires o.owner <= m.m.Keys   //IN-KLON
//   requires o.AMFO  <= m.m.Keys   //IN-KLON
//
//   reads m.oHeap`fields, m.oHeap`fieldModes
//   reads m.ns`fields, m.ns`fieldModes
//   reads m.m.Keys`fields, m.m.Keys`fieldModes
{
  var c := m.m[o];

  && (c.bound == mapThruKlown(o.bound, m))
  && (c.AMFB  == mapThruKlown(o.AMFB,  m))
  && (c.owner == mapThruKlown(o.owner, m))
  && (c.AMFX  == mapThruKlown(o.AMFX , m))
  && (c.ntrnl == mapThruKlown(o.ntrnl, m))
  && (c.AMFO  == mapThruKlown(o.AMFO,  m))
}




lemma  mapThruKlownMapsOK1(k : Object, v : Object, m : Klon)
  //again moved from m.o+amfo to m.o_amfx
  requires m.readyAll()   //KLON-OK
  requires m.readyOK(k)
  requires k in m.m.Keys
  requires m.m[k] == v
  requires k.Ready()
  requires m.m.Keys >= k.ntrnl > k.owner >= k.bound  //IN-KLON
  requires m.m.Keys >= k.AMFO  > k.AMFX  >= k.AMFB   //IN-KLON
  requires k.owner <= m.m.Keys   //IN-KLON
  requires k.AMFO  <= m.m.Keys   //IN-KLON

  requires k.owner <= m.m.Keys   //IN-KLON
  requires k.AMFO  <= m.m.Keys   //IN-KLON
  requires mappingOwnersThruKlownOK(k,m)
  ensures (
    var mTKoA := mapThruKlon(m.o_amfx, m);
    var CXTRA := m.c_amfx - mTKoA;
    var OXTRA := mTKoA - m.c_amfx;
    && ((mTKoA - OXTRA + CXTRA) == m.c_amfx)
    && (v.AMFO == mapThruKlown(k.AMFO,m))
  )
{
    var mTKoA := mapThruKlon(m.o_amfx, m);
    var CXTRA := m.c_amfx - mTKoA;
    var OXTRA := mTKoA - m.c_amfx;
    assert
      && ((mTKoA - OXTRA + CXTRA) == m.c_amfx)
      && (v.AMFO == mapThruKlown(k.AMFO,m))
      ;
}



lemma  mapThruKlownMapsOK2(o : Object,  m' : Klon, m : Klon)
  //given allMapOwnersThruKlownOK(m') and klonLEQ(m',m), establish mappingOwnersThruKlownOK(o,m)

  //reqs from mappingOwnersThruKlownOK()
  requires m'.m.Keys >= o.ntrnl > o.owner >= o.bound  //IN-KLON
  requires m'.m.Keys >= o.AMFO  > o.AMFX  >= o.AMFB   //IN-KLON
  requires m'.o_amfx <= m'.m.Keys   //KLON-OK
  requires o in m'.m.Keys
  requires m'.ownersInKlown(o) //or could be objectInKlown...
  //end reqs from mappingOwnersThruKlownOK()

  requires mappingOwnersThruKlownOK(o,m')
  requires klonLEQ(m',m)

  ensures   mappingOwnersThruKlownOK(o,m)
  {}


lemma mapThruKlownMapsOK3(o : Object, m : Klon)
  //given allMapOwnersThruKlownOK(m), and o in m.m.Keys establish mappingOwnersThruKlownOK(o,m)

  //reqs from allMapOwnersThruKlownOK
  requires m.readyAll()
  requires m.readyAll() //KLON-OK
  requires forall o <- m.m.Keys :: m.readyOK(o)
  requires forall o <- m.m.Keys :: m.ownersInKlown(o)  //same as objectInKlown
  //end reqs from allMapOwnersThruKlownOK

  requires o in m.m.Keys  //IN-KLON
  requires m.m.Keys >= o.ntrnl > o.owner >= o.bound  //IN-KLON
  requires m.m.Keys >= o.AMFO  > o.AMFX  >= o.AMFB   //IN-KLON

  requires allMapOwnersThruKlownOK(m)

  ensures  mappingOwnersThruKlownOK(o,m)
{}

lemma mapThruKlownMapsOK4(o : Object, m : Klon)
  //given allMapOwnersThruKlownOK(m), and o in m.m.Keys establish o.Ready()

  //reqs from allMapOwnersThruKlownOK
  requires m.readyAll()
  requires m.readyAll() //KLON-OK
  requires forall o <- m.m.Keys :: m.readyOK(o)
  requires forall o <- m.m.Keys :: m.ownersInKlown(o)  //same as objectInKlown
  //end reqs from allMapOwnersThruKlownOK

  requires o in m.m.Keys  //IN-KLON
  requires m.m.Keys >= o.ntrnl > o.owner >= o.bound  //IN-KLON
  requires m.m.Keys >= o.AMFO  > o.AMFX  >= o.AMFB   //IN-KLON

  requires allMapOwnersThruKlownOK(m)

  ensures  o.Ready()
{
    assert allMapOwnersThruKlownOK(m);
    assert o in m.m.Keys;
    mapThruKlownMapsOK3(o, m);
    assert mappingOwnersThruKlownOK(o,m);
    m.ReadyOKDUCKED(o);

    assert o.Ready();
}


predicate {:isolate_assertions} allMapOwnersThruKlownOK(m : Klon) : (rv : bool)

  requires m.readyAll() //KLON-OK
  requires forall o <- m.m.Keys :: m.readyOK(o)
  requires forall o <- m.m.Keys :: m.ownersInKlown(o)  //same as objectInKlown
//
//   requires forall o <- m.m.Keys :: (
//         && (m.readyAll())   //KLON-OK
//         && (m.readyOK(o))
//         && (KLUCKO(o,m); o.Ready())//BUGGY!
//         && (o.Ready())
//         && (m.m.Keys >= o.bound)
//         && (m.m.Keys >= o.ntrnl > o.owner >= o.bound ) //IN-KLON
//         && (m.m.Keys >= o.AMFO  > o.AMFX  >= o.AMFB )  //IN-KLON
//         && (o.owner <= m.m.Keys)   //IN-KLON
//         && (o.AMFO  <= m.m.Keys)   //IN-KLON
  // )
  // reads m.oHeap`fields, m.oHeap`fieldModes
  // reads m.ns`fields, m.ns`fieldModes
  // reads m.m.Keys`fields, m.m.Keys`fieldModes
  // reads m.o`fields, m.o`fieldModes
{
  //  forall o <- m.m.Keys :: mappingOwnersThruKlownOK(o,m)

  forall o <- m.m.Keys :: mappingOwnersThruKlownOK(o,m)

//         var c := m.m[o];
//
//         assert m.m.Keys > o.AMFX;
//
//        && (c.bound == mapThruKlown(o.bound, m))
//        && (c.AMFB  == mapThruKlown(o.AMFB,  m))
//        && (c.owner == mapThruKlown(o.owner, m))
//        && (c.AMFX  == mapThruKlown(o.AMFX , m))
//        && (c.ntrnl == mapThruKlown(o.ntrnl, m))
//        && (c.AMFO  == mapThruKlown(o.AMFO,  m))
//



}


lemma allMapOwnersThruKlownKV(m' : Klon, k : Object, v : Object, m : Klon)
//Horrible name, but OKs adding a new cloned object into the klon.
//ensures m'[k := v] == m
  requires k !in m'.m.Keys
  requires v !in m'.m.Values
  requires k  in m'.oHeap
  requires m'.ownersInKlown(k)
  requires klonCanKV(m',k,v)
  requires m == klonKV(m',k,v)
  requires m.from(m')

  // requires forall k <- m'.m.Keys :: k.owner <= m'.m.Keys   //IN-KLON
  // requires forall k <- m'.m.Keys :: k.AMFO  <= m'.m.Keys   //IN-KLON

  requires m'.readyAll()
  requires m'.o_amfx <= m'.m.Keys   //KLON-OK
  requires forall o <- m'.m.Keys :: m'.readyOK(o)
  requires forall o <- m'.m.Keys :: m'.ownersInKlown(o) ///coiiudl we be objectsInKnown...
  requires allMapOwnersThruKlownOK(m')

  requires k.Ready()

  requires m.m.Keys >= k.bound
  requires m.m.Keys >= k.ntrnl > k.owner >= k.bound  //IN-KLON
  requires m.m.Keys >= k.AMFO  > k.AMFX  >= k.AMFB   //IN-KLON
  requires k.owner <= m.m.Keys   //IN-KLON
  requires k.AMFO  <= m.m.Keys   //IN-KLON

  requires canMapOwnersThruKlown(k,m)
  requires KMOKM: mappingOwnersThruKlownOK(k,m) //THIS iS A BIT WEIRD as a "requires".. but

  //preconds of allMapOwnersThruKlownOK(m)
  requires m.readyAll()
  // requires m.readyAll() //KLON-OK
  // requires forall o <- m.m.Keys :: m.objectInKlown(o)

  ensures  allMapOwnersThruKlownOK(m)
{
  assert v == m.m[k];
  assert forall mm <- m'.m.Keys :: m'.m[mm]  == m.m[mm];
  assert forall mm <- m.m.Keys :: ((mm in m'.m.Keys) ==> (m'.m[mm] == m.m[mm]));

  assert m.m.Keys == m'.m.Keys + {k};

   assert allMapOwnersThruKlownOK(m');

   forall mm <- m'.m.Keys ensures mappingOwnersThruKlownOK(mm, m) //by
   {
      assert mappingOwnersThruKlownOK(mm, m');
      mapThruKlownMapsOK2(mm, m', m);
      assert mappingOwnersThruKlownOK(mm, m);
   }

   forall mm <- m.m.Keys ensures mappingOwnersThruKlownOK(mm, m) //by
   {
    if (mm == k) { reveal KMOKM; assert mappingOwnersThruKlownOK(k, m); }
      else { assert mappingOwnersThruKlownOK(mm, m); }
   }

   assert allMapOwnersThruKlownOK(m);
}


lemma {:isolate_assertions} AllKlownPreservesOwnership(m : Klon)

  //preconds or allMapOwnersThruKlownOK(m)
  requires m.readyAll() //KLON-OK

  requires allMapOwnersThruKlownOK(m)
  requires forall k <- m.m.Keys :: k.owner <= m.m.Keys   //IN-KLON
  requires forall k <- m.m.Keys :: k.AMFO  <= m.m.Keys   //IN-KLON
  requires m.readyAll()//KLON-OK


  ensures forall i <- m.m.Keys, j <- m.m.Keys ::  (insideCompatible(i,j,m.m[i],m.m[j],m))

  {
assert forall i <- m.m.Keys :: mappingOwnersThruKlownOK(i,m);

forall i <- m.m.Keys, j <- m.m.Keys
  ensures (insideCompatible(i,j,m.m[i],m.m[j],m))
  {
    if (i == j) { return; }
    if (inside(i,j)) {
        assert i.AMFO >= j.AMFO;
        assert mappingOwnersThruKlownOK(i,m);
        assert mappingOwnersThruKlownOK(j,m);
    }
    assert (insideCompatible(i,j,m.m[i],m.m[j],m));
  }

//  assert forall i <- m.m.Keys, j <- m.m.Keys ::  (insideCompatible(i,j,m.m[i],m.m[j],m));

  }



lemma {:isolate_assertions} AllKlownPreservesReferences(m : Klon)

  //preconds or allMapOwnersThruKlownOK(m)
  requires m.readyAll()
  requires m.readyAll() //KLON-OK

  requires allMapOwnersThruKlownOK(m)
  requires forall k <- m.m.Keys :: k.owner <= m.m.Keys   //IN-KLON
  requires forall k <- m.m.Keys :: k.AMFO  <= m.m.Keys   //IN-KLON
  requires m.readyAll()//KLON-OK

  requires forall i <- m.m.Keys, j <- m.m.Keys ::  (insideCompatible(i,j,m.m[i],m.m[j],m))

  ensures  forall i <- m.m.Keys, j <- m.m.Keys ::  (refOK(i,j) ==> refOK(m.m[i],m.m[j]))

  {
assert forall i <- m.m.Keys :: mappingOwnersThruKlownOK(i,m);


forall i <- m.m.Keys, j <- m.m.Keys
  ensures (refOK(i,j) ==> refOK(m.m[i],m.m[j]))
  {
    if refOK(i,j) {
      if (i == j) {
        assert refOK(m.m[i],m.m[j]);
      } else if (refBI(i,j)) {
          assert refBI(m.m[i],m.m[j]);
          assert refOK(m.m[i],m.m[j]);
      } else if (refDI(i,j)) {
          assert refDI(m.m[i],m.m[j]);
          assert refOK(m.m[i],m.m[j]);
      } else {
        assert {:contradiction} not(refOK(i,j));
        assert {:contradiction} false;
      }
    }
    assert (refOK(i,j) ==> refOK(m.m[i],m.m[j]));
  }




  }








predicate insideCompatible(of : Object, ot : Object, cf : Object, ct: Object, m : Klon) : ( rv : bool )
  //clone's inside is compatible with original's inside
  requires {of, ot} <= m.m.Keys
  requires m.m[of] == cf
  requires m.m[ot] == ct
{
  (inside(of,ot) ==> inside(cf,ct))
}



//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
// paranoid self-consistency checks


lemma MoreValidThanValid(o : Object)
  requires o.Ready()
  ensures  o !in o.AMFB
  ensures  o !in o.AMFX
  ensures  o  in o.AMFO
{}

lemma OOOLDEInside3(a : Object, b : Object, c : Object)
  requires inside(a,b)
  requires inside(b,c)
  ensures  inside(a,c)
{}






//diversion -BI & DI definitions cross with flattness
//predicate fefBI(f : Object, t : Object) {flatten(f.bound) >= flatten(t.owner)}

lemma recBIvsfefBI(f : Object, t : Object)
  requires f.Ready()
  requires t.Ready()
  ensures refBI(f,t) == fefBI(f,t)
{}

lemma recBIvsFLAT(f : Object, t : Object)
  requires f.Ready()
  requires t.Ready()
  ensures (f.AMFB >= t.AMFX) <==> (flatten(f.bound) >= flatten(t.owner))
  ensures refBI(f,t) == fefBI(f,t)
{}

lemma recDIvsFLAT(f : Object, t : Object)
  requires f.Ready()
  requires t.Ready()
  ensures (f.AMFO == t.AMFX) ==> ((flatten(f.ntrnl - {f}) + {f})  == flatten(t.owner))
{}


lemma refBI_nesting(a : Object, b : Object, c : Object, m : Klon)
  requires a.Ready()
  requires b.Ready()
  requires c.Ready()

  requires refBI(a,b)

  ensures  (a.AMFO > a.AMFX >= a.AMFB)
  ensures  (b.AMFO > b.AMFX >= b.AMFB)
  ensures  a.AMFB >= b.AMFX
  ensures  (a.AMFO > a.AMFX >= a.AMFB >= b.AMFX >= b.AMFB)
  ensures  a.AMFB >= b.AMFB
{}

lemma refBI_transitive(a : Object, b : Object, c : Object, m : Klon)
  requires a.Ready()
  requires b.Ready()
  requires c.Ready()

  requires refBI(a,b)
  requires refBI(b,c)

  ensures  refBI(a,c)
{}

//end diversion


//
// inside vs inside
//

predicate recInside(part : Object, whole : Object) : (r : bool)
    requires part.Ready()
    decreases part.AMFO
{
  || (part == whole)
  || (exists x <- part.owner :: recInside(x,whole))
}

function collectAllOwners(o : Object) : (rv : Owner)
  decreases o.AMFO
  requires o.Ready()
{
  {o} + o.owner + (set xo <- o.owner, co <- collectAllOwners(xo) :: co)
}

lemma collectAllAMFO(o : Object)
  decreases o.AMFO
  requires  o.Ready()
  ensures   o.AMFO == collectAllOwners(o)
  {}

lemma recInsideCollectsAllOwners1(part : Object, whole : Object)
  decreases part.AMFO
  requires part.Ready()
  requires recInside(part,whole)
  ensures  (whole in collectAllOwners(part))
{}

lemma recInsideCollectsAllOwners2(part : Object, whole : Object)
  decreases part.AMFO
  requires part.Ready()
  ensures recInside(part,whole) <== (whole in collectAllOwners(part))
{}







lemma recInsideAMFO1(part : Object, whole : Object)
  decreases part.AMFO
  requires part.Ready()
  requires whole.Ready() //why not?

  requires (whole in part.AMFO)
  ensures  recInside(part,whole)
{}

lemma recInsideAMFO2(part : Object, whole : Object)
  decreases part.AMFO
  requires  part.Ready()
  requires  whole.Ready() //why not?
  requires  recInside(part,whole)
  ensures   (whole in part.AMFO)
{}

lemma InsideRecInside1(part : Object, whole : Object)
   requires part.Ready()
   requires whole.Ready() //why not?
   requires recInside(part,whole)
   ensures  inside(part,whole)
   {
      recInsideCollectsAllOwners1(part,whole);
      assert (whole in collectAllOwners(part));
      collectAllAMFO(part);
      assert (whole in part.AMFO);
      AXIOMAMFO(part, whole);
   }


lemma InsideRecInside2(part : Object, whole : Object)
   requires part.Ready()
   requires whole.Ready() //why not?
   requires    inside(part,whole)
   ensures  recInside(part,whole)
   {
    assert  inside(part,whole);
    assert  part.AMFO >= whole.AMFO;
    AXIOMAMFOREVERSE(part,whole);
    assert whole in part.AMFO;
    collectAllAMFO(part);
    assert (whole in collectAllOwners(part));
    recInsideCollectsAllOwners2(part,whole);
    assert recInside(part,whole);
   }



///////////////////////////////////////////////////////////////////////////////////////////
// the Pointing Lemmas
///////////////////////////////////////////////////////////////////////////////////////////
//
lemma INSIDE_CAN_POUNT_OUT(m' : Klon, f : Object, t : Object, o : Object, c : Object)
 requires f.Ready()
 requires o.Ready()
 requires t.Ready()
 requires inside(f,o)
 requires outside(t,o)
 //requires |f.AMFO| == |o.AMFO| + 100   ///arbitrarily deep

 requires refOK(o,t)
 requires f.AMFB >= t.AMFX
 ensures  refOK(f,t)
{
  // assert refOK(o,t);

//   assert (o==t) || refBI(o,t) || refDI(o,t);
//
//   assert (o != t);
//
//   if (refDI(o,t)) {
//       assert {:contradiction} o.AMFO == t.AMFX;
//       assert {:contradiction} t.AMFO == (t.AMFX + {t});
//       assert {:contradiction} t.AMFO > o.AMFO;
//       assert {:contradiction} inside(t,o);
//       assert {:contradiction} false;
//       return;
//   }

  // assert refBI(o,t); //only remaining case
  // assert o.AMFB >= t.AMFX;
  // assert f.AMFB >= t.AMFX;

  // assert refOK(f,t);
}

lemma MOVING_ON_IN(m' : Klon, f : Object, t : Object, o : Object, c : Object)
/// can move an object down; doesn't lose access
 requires f.Ready()
 requires o.Ready()
 requires t.Ready()
 requires inside(c,o) && (c != o)
 requires inside(f,c) && (f != c)
 requires |f.AMFO| == |o.AMFO| + 100
 requires refOK(o,t)
 requires outside(t,o)
 requires f.AMFB >= t.AMFX

 ensures refOK(f,t)
{}

lemma outsideAINTEQUALS(a : Object, b : Object)
  requires outside(a,b)
  ensures  a != b
  {}


lemma InsideOutsideAINTEQUALS(a : Object, b : Object, o : Object)
  requires a.Ready()
  requires b.Ready()
  requires o.Ready()
  requires inside(a,o)
  requires outside(b,o)
  ensures  a != b
  {}

lemma NO_INCOMING_REFS(f : Object, t : Object, o : Object)
 requires f.Ready()
 requires o.Ready()
 requires t.Ready()
 requires outside(f,o) //&& (f != o) //unnecessary
 requires inside(t,o)  && (t != o) //perhaps, perhaps, perhaps  //ieStrictlyInside

 ensures not( refOK(f,t) )
 ensures f != t
{
}

lemma INCOMING_REFS_OWNER_ONLY(f : Object, t : Object, o : Object)
 requires f.Ready()
 requires o.Ready()
 requires t.Ready()
 requires outside(f,o) //&& (f != o) //unnecessary
 requires inside(t,o)  //&& (t != o) //perhaps, perhaps, perhaps  //ieStrictlyInside
 requires refOK(f,o)
 requires refOK(f,t)
 ensures  t == o
 ensures f != t
{}
