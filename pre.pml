proctype ChildProcess()
{
   printf('\\nCP(%d) Started.',id);
   insert_list[0] = 50;
   insert_list[1] = 51;
   insert_list[2] = id;
   insert_list[3] = (id+1);
   insert_list[4] = 60;
   insert_list[5] = 61;
   to_insert = 0;
   max_insert = 5;
   p_state.k = 0;
   p_state.l = 0;
   p_state.m = S_IDLE;
   do
   ::
      ch_HtoP??eval(id),p_input.c,p_input.o;
      cmd = p_input.c;
      ops = p_input.o;
      k = p_state.k;
      l = p_state.l;
      m = p_state.m;
      if
      ::
         ((cmd==1));
         if
         ::
            ((m==S_IDLE));
            if
            ::
               ((ops==O_CONTINUE));
                {
                  printf('\\nCP(%d): (%d,%d,%e)----(%d,%e)---->(%d,%d,%e)',id,p_state.k,p_state.l,p_state.m,cmd,ops,k,l,m);
                  p_state.k = k;
                  p_state.l = l;
                  p_state.m = m;
                };

            ::
               ((ops==O_INSERT));
                {
                  if
                  ::
                     ((to_insert>max_insert));
                     printf('\\nCP(%d): No more insertions!',id);
                     newk = 0;

                  ::
                     else;
                     newk = insert_list[to_insert];
                     to_insert = (to_insert+1);

                  fi;
                };
               if
               ::
                  ((newk==0));
                   {
                     printf('\\nCP(%d): (%d,%d,%e)----(%d,%e)---->(%d,%d,%e)',id,p_state.k,p_state.l,p_state.m,cmd,ops,0,0,1);
                     p_state.k = 0;
                     p_state.l = 0;
                     p_state.m = 1;
                   };

               ::
                  else;
                   {
                     printf('\\nCP(%d): (%d,%d,%e)----(%d,%e)---->(%d,%d,%e)',id,p_state.k,p_state.l,p_state.m,cmd,ops,newk,HEAD,3);
                     p_state.k = newk;
                     p_state.l = HEAD;
                     p_state.m = 3;
                   };

               fi;

            fi;

         ::
            ((m==S_SEARCH));
             {
               next = list[l].next;
               nextval = list[next].value;
               if
               ::
                  ((nextval<k));
                  lnext = next;
                  mnext = S_SEARCH;

               ::
                  ((nextval>=k));
                  lnext = l;
                  mnext = S_INSERT;

               fi;
             };
             {
               printf('\\nCP(%d): (%d,%d,%e)----(%d,%e)---->(%d,%d,%e)',id,p_state.k,p_state.l,p_state.m,cmd,ops,k,lnext,mnext);
               p_state.k = k;
               p_state.l = lnext;
               p_state.m = mnext;
             };

         ::
            ((m==S_INSERT));
             {
               next = list[l].next;
               if
               ::
                  ((list[next].value==k));
                  printf('\\nCP(%d): %d already exists at index %d. Skipping the insert',id,k,next);

               ::
                  else;
                  d_step {
                     current = EMPTY;
                     EMPTY = (EMPTY+1);
                   };
                  d_step {
                     printf('CP(%d): Critical Value (before): %d, a: %d, b: %d,  c:%d',_pid,critical_val,list[l].value,list[next].value,k);
                     critical_val = (((critical_val/(list[next].value-list[l].value))*(k-list[l].value))*(list[next].value-k));
                   };
                  list[current].value = k;
                  list[current].next = next;
                  list[l].next = current;

               fi;
             };
             {
               printf('\\nCP(%d): (%d,%d,%e)----(%d,%e)---->(%d,%d,%e)',id,p_state.k,p_state.l,p_state.m,cmd,ops,0,0,4);
               p_state.k = 0;
               p_state.l = 0;
               p_state.m = 4;
             };

         ::
            ((m==S_OVER));
            printf('\\nCP(%d): Received message in S_OVER state,exiting now..',id);
            goto :b0;

         fi;

      ::
         ((cmd==0));
          {
            printf('\\nCP(%d): (%d,%d,%e)----(%d,%e)---->(%d,%d,%e)',id,p_state.k,p_state.l,p_state.m,cmd,ops,k,l,m);
            p_state.k = k;
            p_state.l = l;
            p_state.m = m;
          };

      fi;
      ch_PtoH!id,p_state.k,p_state.l,p_state.m;
      printf('\\nCP(%d): Message sent (%d, %d, %e)',id,p_state.k,p_state.l,p_state.m);

   od;
:b0:
   printf('\\nCP(%d) Exited.',id);
}
proctype HubController()
{
   printf('\\nHC Started with 2 processes %d and %d.',id1,id2);
   h_state.proc[0].c = 1;
   h_state.proc[0].o = O_INSERT;
   h_state.proc[0].isOver = 0;
   h_state.proc[1].c = 1;
   h_state.proc[1].o = O_INSERT;
   h_state.proc[1].isOver = 0;
    {
      h_send.c = h_state.proc[0].c;
      h_send.o = h_state.proc[0].o;
      ch_HtoP!id1,h_send.c,h_send.o;
      printf('\\nHC: Message sent (%d, %e) to CP(%d)',h_send.c,h_send.o,id1);
    };
    {
      h_send.c = h_state.proc[1].c;
      h_send.o = h_state.proc[1].o;
      ch_HtoP!id2,h_send.c,h_send.o;
      printf('\\nHC: Message sent (%d, %e) to CP(%d)',h_send.c,h_send.o,id2);
    };
   do
   ::
      ch_PtoH??eval(id1),h_input.proc[0].k,h_input.proc[0].l,h_input.proc[0].m;
      if
      ::
         ch_PtoH??eval(id2),h_input.proc[1].k,h_input.proc[1].l,h_input.proc[1].m;
          {
            k1 = h_input.proc[0].k;
            l1 = h_input.proc[0].l;
            m1 = h_input.proc[0].m;
            k2 = h_input.proc[1].k;
            l2 = h_input.proc[1].l;
            m2 = h_input.proc[1].m;
            if
            ::
               ((((m1==S_INSERT)&&(m2==S_INSERT))&&(l1==l2)));
               if
               ::
                  ((k1<k2));
                  c1 = 0;
                  c2 = 1;

               ::
                  ((k1>k2));
                  c1 = 1;
                  c2 = 0;

               ::
                  ((k1==k2));
                  if
                  ::
                     ((k1>0));
                     c1 = 1;
                     c2 = 0;

                  ::
                     ((k2>0));
                     c2 = 1;
                     c1 = 0;

                  fi;

               fi;

            ::
               else;
               c1 = 1;
               c2 = 1;

            fi;
            if
            ::
               ((m1==S_OVER));
               isOver1 = 1;

            ::
               else;
               isOver1 = 0;

            fi;
            if
            ::
               ((m2==S_OVER));
               isOver2 = 1;

            ::
               else;
               isOver2 = 0;

            fi;
            if
            ::
               ((m1==S_IDLE));
               o1 = O_INSERT;

            ::
               else;
               o1 = O_CONTINUE;

            fi;
            if
            ::
               ((m2==S_IDLE));
               o2 = O_INSERT;

            ::
               else;
               o2 = O_CONTINUE;

            fi;
            printf('\\nHC: [(%d,%e,%d),(%d,%e,%d)]----[(%d,%d,%e),(%d,%d,%e)]---->[(%d,%e,%d),(%d,%e,%d)]',h_state.proc[0].c,h_state.proc[0].o,h_state.proc[0].isOver,h_state.proc[1].c,h_state.proc[1].o,h_state.proc[1].isOver,h_input.proc[0].k,h_input.proc[0].l,h_input.proc[0].m,h_input.proc[1].k,h_input.proc[1].l,h_input.proc[1].m,c1,o1,isOver1,c2,o2,isOver2);
            h_state.proc[0].c = c1;
            h_state.proc[0].o = o1;
            h_state.proc[0].isOver = isOver1;
            h_state.proc[1].c = c2;
            h_state.proc[1].o = o2;
            h_state.proc[1].isOver = isOver2;
          };
          {
            h_send.c = h_state.proc[0].c;
            h_send.o = h_state.proc[0].o;
            ch_HtoP!id1,h_send.c,h_send.o;
            printf('\\nHC: Message sent (%d, %e) to CP(%d)',h_send.c,h_send.o,id1);
          };
          {
            h_send.c = h_state.proc[1].c;
            h_send.o = h_state.proc[1].o;
            ch_HtoP!id2,h_send.c,h_send.o;
            printf('\\nHC: Message sent (%d, %e) to CP(%d)',h_send.c,h_send.o,id2);
          };

      ::
         ((h_state.proc[1].isOver==1));
          {
            c1 = 1;
            if
            ::
               ((h_input.proc[0].m==S_OVER));
               isOver1 = 1;

            ::
               else;
               isOver1 = 0;

            fi;
            if
            ::
               ((h_input.proc[0].m==S_IDLE));
               o1 = O_INSERT;

            ::
               else;
               o1 = O_CONTINUE;

            fi;
            printf('\\nHC: [(%d,%e,%d),(S_OVER)]----[(%d,%d,%e),(S_OVER))]---->[(%d,%e,%d),(S_OVER)]',h_state.proc[0].c,h_state.proc[0].o,h_state.proc[0].isOver,h_input.proc[0].k,h_input.proc[0].l,h_input.proc[0].m,c1,o1,isOver1);
            h_state.proc[0].c = c1;
            h_state.proc[0].o = o1;
            h_state.proc[0].isOver = isOver1;
          };
          {
            h_send.c = h_state.proc[0].c;
            h_send.o = h_state.proc[0].o;
            ch_HtoP!id1,h_send.c,h_send.o;
            printf('\\nHC: Message sent (%d, %e) to CP(%d)',h_send.c,h_send.o,id1);
          };

      fi;

   ::
      ch_PtoH??eval(id2),h_input.proc[1].k,h_input.proc[1].l,h_input.proc[1].m;
      if
      ::
         ch_PtoH??eval(id1),h_input.proc[0].k,h_input.proc[0].l,h_input.proc[0].m;
          {
            k1 = h_input.proc[0].k;
            l1 = h_input.proc[0].l;
            m1 = h_input.proc[0].m;
            k2 = h_input.proc[1].k;
            l2 = h_input.proc[1].l;
            m2 = h_input.proc[1].m;
            if
            ::
               ((((m1==S_INSERT)&&(m2==S_INSERT))&&(l1==l2)));
               if
               ::
                  ((k1<k2));
                  c1 = 0;
                  c2 = 1;

               ::
                  ((k1>k2));
                  c1 = 1;
                  c2 = 0;

               ::
                  ((k1==k2));
                  if
                  ::
                     ((k1>0));
                     c1 = 1;
                     c2 = 0;

                  ::
                     ((k2>0));
                     c2 = 1;
                     c1 = 0;

                  fi;

               fi;

            ::
               else;
               c1 = 1;
               c2 = 1;

            fi;
            if
            ::
               ((m1==S_OVER));
               isOver1 = 1;

            ::
               else;
               isOver1 = 0;

            fi;
            if
            ::
               ((m2==S_OVER));
               isOver2 = 1;

            ::
               else;
               isOver2 = 0;

            fi;
            if
            ::
               ((m1==S_IDLE));
               o1 = O_INSERT;

            ::
               else;
               o1 = O_CONTINUE;

            fi;
            if
            ::
               ((m2==S_IDLE));
               o2 = O_INSERT;

            ::
               else;
               o2 = O_CONTINUE;

            fi;
            printf('\\nHC: [(%d,%e,%d),(%d,%e,%d)]----[(%d,%d,%e),(%d,%d,%e)]---->[(%d,%e,%d),(%d,%e,%d)]',h_state.proc[0].c,h_state.proc[0].o,h_state.proc[0].isOver,h_state.proc[1].c,h_state.proc[1].o,h_state.proc[1].isOver,h_input.proc[0].k,h_input.proc[0].l,h_input.proc[0].m,h_input.proc[1].k,h_input.proc[1].l,h_input.proc[1].m,c1,o1,isOver1,c2,o2,isOver2);
            h_state.proc[0].c = c1;
            h_state.proc[0].o = o1;
            h_state.proc[0].isOver = isOver1;
            h_state.proc[1].c = c2;
            h_state.proc[1].o = o2;
            h_state.proc[1].isOver = isOver2;
          };
          {
            h_send.c = h_state.proc[0].c;
            h_send.o = h_state.proc[0].o;
            ch_HtoP!id1,h_send.c,h_send.o;
            printf('\\nHC: Message sent (%d, %e) to CP(%d)',h_send.c,h_send.o,id1);
          };
          {
            h_send.c = h_state.proc[1].c;
            h_send.o = h_state.proc[1].o;
            ch_HtoP!id2,h_send.c,h_send.o;
            printf('\\nHC: Message sent (%d, %e) to CP(%d)',h_send.c,h_send.o,id2);
          };

      ::
         ((h_state.proc[0].isOver==1));
          {
            c1 = 1;
            if
            ::
               ((h_input.proc[1].m==S_OVER));
               isOver1 = 1;

            ::
               else;
               isOver1 = 0;

            fi;
            if
            ::
               ((h_input.proc[1].m==S_IDLE));
               o1 = O_INSERT;

            ::
               else;
               o1 = O_CONTINUE;

            fi;
            printf('\\nHC: [(%d,%e,%d),(S_OVER)]----[(%d,%d,%e),(S_OVER))]---->[(%d,%e,%d),(S_OVER)]',h_state.proc[1].c,h_state.proc[1].o,h_state.proc[1].isOver,h_input.proc[1].k,h_input.proc[1].l,h_input.proc[1].m,c1,o1,isOver1);
            h_state.proc[1].c = c1;
            h_state.proc[1].o = o1;
            h_state.proc[1].isOver = isOver1;
          };
          {
            h_send.c = h_state.proc[1].c;
            h_send.o = h_state.proc[1].o;
            ch_HtoP!id2,h_send.c,h_send.o;
            printf('\\nHC: Message sent (%d, %e) to CP(%d)',h_send.c,h_send.o,id2);
          };

      fi;

   ::
      (((h_state.proc[0].isOver==1)&&(h_state.proc[1].isOver==1)));
      printf('\\nHC: We should exit - both processes are done!');
      goto :b1;

   od;
:b1:
   if
   ::
      (0);
      printf('\\nHC Exited');

   fi;
}
proctype parent()
{
   n = _nr_pr;
   x = 0;
    {
      HEAD = (0+1);
      TAIL = (0+2);
      list[HEAD].value = 0;
      list[HEAD].next = TAIL;
      list[TAIL].value = 255;
      list[TAIL].next = 0;
      printf('\\nCritical Value: %d',critical_val);
    };
    {
      i = HEAD;
      printf('\\nBegin List\\n');
      do
      ::
         (1);
         next = list[i].next;
         if
         ::
            ((i!=HEAD));
            printf('\\n--(%d, %d, %d)\\n',i,list[i].value,list[i].next);
            assert((list[i].value!=list[next].value));

         ::
            else;
            printf('\\n--Head Node\\n');

         fi;
         if
         ::
            ((next==TAIL));
            goto :b2;

         ::
            else;
            i = next;

         fi;

      od;
:b2:
      printf('\\nEnd List\\n');
    };
    {
      i = HEAD;
      printf('\\nStart Memory print\\n');
      i = HEAD;
      do
      ::
         ((i<=EMPTY));
         printf('\\nLocation: %d, Value: %d, Next: %d',i,list[i].value,list[i].next);
         i = (i+1);

      ::
         else;
         goto :b3;

      od;
:b3:
      printf('\\nEnd Memory print\\n');
    };
   (run ChildProcess(1));
   (run ChildProcess(2));
   (run HubController(1,2));
   ((n==_nr_pr));
    {
      i = HEAD;
      printf('\\nBegin List\\n');
      do
      ::
         (1);
         next = list[i].next;
         if
         ::
            ((i!=HEAD));
            printf('\\n--(%d, %d, %d)\\n',i,list[i].value,list[i].next);
            assert((list[i].value!=list[next].value));

         ::
            else;
            printf('\\n--Head Node\\n');

         fi;
         if
         ::
            ((next==TAIL));
            goto :b4;

         ::
            else;
            i = next;

         fi;

      od;
:b4:
      printf('\\nEnd List\\n');
    };
    {
      i = HEAD;
      printf('\\nStart Memory print\\n');
      i = HEAD;
      do
      ::
         ((i<=EMPTY));
         printf('\\nLocation: %d, Value: %d, Next: %d',i,list[i].value,list[i].next);
         i = (i+1);

      ::
         else;
         goto :b5;

      od;
:b5:
      printf('\\nEnd Memory print\\n');
    };
}
