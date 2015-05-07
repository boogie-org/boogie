type T = bv4;
function {:bvbuiltin "bvult"} bvlt(p1: T, p2: T) : bool; // unsigned less than
function {:bvbuiltin "bvxor"} xorT(p1: T, p2: T) : T;
function {:bvbuiltin "bvadd"} bvadd(p1: T, p2: T) : T;


procedure bar({:visible} v: T)
  returns ({:hidden} h: T)
  ensures true;
{
  h := v;
}

procedure foo0({:visible} x1: T, {:visible} x2: T, {:hidden} y1: T, {:hidden} y2: T)
  returns ({:visible} r1: bool, {:visible} r2: bool, 
      {:visible} s1: T, {:visible} s2: T, {:visible} s3: T, {:visible} s4: T)
  ensures (r2 == bvlt(bvadd(x1,x2), bvadd(y1,y2))) && (r1 == bvlt(x1, y1));
{
   var {:hidden} t1, t2: T;

   r1 := bvlt(x1, y1);

   havoc s1;
   havoc s2;

   s3 := xorT(x1, s1);
   s4 := xorT(y1, s2);

   t1 := xorT(s1, s3);
   t2 := xorT(s2, s4);

   r2 := bvlt(bvadd(x2, t1), bvadd(y2, t2));
}


procedure foo1({:visible} x1: T, {:visible} x2: T, {:hidden} y1: T, {:hidden} y2: T)
  returns ({:visible} r1: bool, {:visible} r2: bool, 
      {:visible} s1: T, {:visible} s2: T, {:hidden} s3: T, {:hidden} s4: T)
  ensures (r2 == bvlt(bvadd(x1,x2), bvadd(y1,y2))) && (r1 == bvlt(x1, y1));
{
   var {:hidden} t1, t2: T;

   r1 := bvlt(x1, y1);

   havoc s1;
   havoc s2;

   s3 := xorT(x1, s1);
   s4 := xorT(y1, s2);

   t1 := xorT(s1, s3);
   t2 := xorT(s2, s4);

   r2 := bvlt(bvadd(x2, t1), bvadd(y2, t2));
}



procedure foo2({:visible} x1: T, {:visible} x2: T, {:hidden} y1: T, {:hidden} y2: T)
  returns ({:visible} r1: bool, {:visible} r2: bool, 
      {:visible} s1: T, {:visible} s2: T)
  ensures (r2 == bvlt(bvadd(x1,x2), bvadd(y1,y2))) && (r1 == bvlt(x1, y1)); 
{
   var {:hidden} t1, t2: T;
   var {:hidden} s3, s4: T;

   r1 := bvlt(x1, y1);

   havoc s1;
   havoc s2;

   s3 := xorT(x1, s1);
   s4 := xorT(y1, s2);

   t1 := xorT(s1, s3);
   t2 := xorT(s2, s4);

   r2 := bvlt(bvadd(x2, t1), bvadd(y2, t2));
}

procedure foo3({:visible} x1: T, {:visible} x2: T, {:hidden} y1: T, {:hidden} y2: T)
  returns ({:visible} r1: bool, {:visible} r2: bool, 
      {:visible} s1: T, {:visible} s2: T, {:hidden} s3: T, {:hidden} s4: T)
  ensures (r2 == bvlt(bvadd(x1,x2), bvadd(y1,y2))) && (r1 == bvlt(x1, y1)) && (s4 == xorT(y1,s2)) && (s3 == xorT(x1, s1));
{
   var {:hidden} t1, t2: T;

   r1 := bvlt(x1, y1);

   havoc s1;
   havoc s2;

   s3 := xorT(x1, s1);
   s4 := xorT(y1, s2);

   t1 := xorT(s1, s3);
   t2 := xorT(s2, s4);

   r2 := bvlt(bvadd(x2, t1), bvadd(y2, t2));
}



procedure bid({:visible} x1: T, {:visible} x2: T, {:hidden} y1: T, {:hidden} y2: T)
  returns ({:visible} r: bool)
  ensures r == bvlt(bvadd(x1,x2), bvadd(y1,y2));
{
  var {:hidden} r1, r2: bool;
  var {:hidden} s1, s2, s3, s4: T;

  call r1, r2, s1, s2, s3, s4 := foo1(x1, x2, y1, y2);

  r := r2;
}


