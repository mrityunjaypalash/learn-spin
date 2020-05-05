spin: concurrentds1.pml:87, Error: missing array index for 'list'	saw '')' = 41'
spin: concurrentds1.pml:88, Error: missing array index for 'list'	saw '')' = 41'
spin: concurrentds1.pml:89, Error: missing array index for 'list'	saw '',' = 44'
proctype P()
{
    {
      HEAD = (0+1);
      TAIL = (0+2);
      list[HEAD].value = 0;
      list[HEAD].next = TAIL;
      list[TAIL].value = 255;
      list[TAIL].next = 0;
    };
    {
      i = HEAD;
      do
      ::
         (1);
         printf('Value: %d, Next Id: %d\\n',i,list[i].value);
         next = list[i].next;
         if
         ::
            ((next==TAIL));
            goto :b0;

         ::
            else;
            i = next;

         fi;

      od;
:b0:
    };
    {
      i = HEAD;
      do
      ::
         (1);
         next = (i+1);
         if
         ::
            ((list[next].value>=5));
            current = EMPTY;
            EMPTY = (EMPTY+1);
            list[current].value = 5;
            list[current].next = next;
            list[i].next = current;
            goto :b1;

         ::
            else;
            i = (i+1);

         fi;

      od;
:b1:
    };
}
