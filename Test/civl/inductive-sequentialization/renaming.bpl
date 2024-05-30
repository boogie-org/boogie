// RUN: %parallel-boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// UNSUPPORTED: batch_mode

// async left action {:layer 1} main()
// refines {:IS_right} main' using Inv;
// creates main;
// {
//     if(*){
//     }
//     else{
//       call create_async(main());
//     }
// }

// async left action {:layer 2} main'()
// creates main';
// {
//   if(*){
//     }
//     else{
//       call create_async(main'());
//     }
// }

// action {:layer 1} Inv()
// creates main;
// {
//     if(*){
//     }
//     else{
//       call create_async(main());
//       call set_choice(main());
//     }
// }

///////////// Version 2

async left action {:layer 1} main()
refines {:IS_right} main' using Inv;
creates main;
{
      call create_async(main());
}

async left action {:layer 2} main'()
creates main';
{
      call create_async(main'());
}

action {:layer 1} Inv()
creates main;
{
      call create_async(main());
      call set_choice(main());
}
