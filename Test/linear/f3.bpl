procedure A() {}

procedure B({:linear ""} tid:int) returns({:linear ""} tid':int)
{
  tid' := tid;
  call A();
}

