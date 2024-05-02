// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

async left action {:layer 1} main_f''()
refines final using Inv;
creates main_f'';
{
    if(*){
    }
    else{
      call create_async(main_f''());
    }
}

action {:layer 2} final()
{
  
}

action {:layer 1} Inv()
creates main_f'';
{
    if(*){
    }
    else{
      call create_async(main_f''());
      call set_choice(main_f''());
    }
}