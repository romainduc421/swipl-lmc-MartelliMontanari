include(main).
:- consult(main).
:- style_check(-singleton).
%test rules

:- begin_tests(regle).
%rename
test(rename) :- regle(X ?= T, R). %R = rename
test(rename, [fail]) :- regle(X ?= a, rename).
test(rename, [fail]) :- regle(X ?= f(a), rename).
test(rename, [fail]) :- regle(X ?= f(X), rename).

%simplify
test(simplify) :- regle(X ?=t, R). %R = simplify
test(simplify) :- regle(X?=a, simplify). %true
test(simplify, [fail]) :- regle(X?=f(a), simplify).
test(simplify, [fail]) :- regle(X ?= f(X), simplify).

%check
test(check) :- regle(X?=f(X),R).  %R = check.
test(check, [fail]):- regle(X ?= a, check).
test(check, [fail]):- regle(X ?= f(a), check).
test(check):- regle(X ?= f(X), check).  %true

%orient
test(orient) :- regle(t ?= X, R).   %R = orient
test(orient) :- regle(t ?= X, orient).  %true
test(orient, [fail]) :- regle(X ?= f(a), orient).
test(orient, [fail]) :- regle(X ?= a, orient).

%decompose
test(decompose) :- regle(f(t) ?= f(X), R).  %R = decompose
test(decompose, [fail]) :- regle(f(X) ?= X, decompose).
test(decompose, [fail]) :- regle(f(X) ?= f(X, Y), decompose).
test(decompose) :- regle(f(X) ?= f(a), decompose).  %true
test(decompose, [fail]) :- regle(f(X) ?= g(Y), decompose).

%clash
test(clash) :- regle(f(t) ?= g(X, a), R).   %R = clash
test(clash, [fail]) :- regle(f(X) ?= X, clash).
test(clash) :- regle(f(X) ?= f(X, Y), clash).   %true
test(clash, [fail]):- regle(f(X) ?= f(a), clash).
test(clash) :- regle(f(X) ?= g(Y), clash).  %true

%expand
test(expand) :- regle(X?=f(a,b),expand).    %true
test(expand, [fail]) :- regle(X?=f(a,b,X),expand).
test(expand, [fail]) :- regle(X?=f(f(a),b,X),expand).
test(expand, [fail]) :- regle(X?=f(f(X,b,a),b,a),expand).
test(expand) :- regle(X?=f(f(Y,b,a),b,a),expand).   %true
test(expand, [fail]) :- regle(X?=f(g(X,b,a),b,a),expand).
test(expand, [fail]) :- regle(X?=f(g(h(X),b,a),b,a),expand).
test(expand) :- regle(X?=f(g(h(Y),b,a),b,a),expand).    %true

:- end_tests(regle).

%%tests reduit
:- begin_tests(reduit).

%rename
test(rename) :- reduit(rename, X ?= T, [], Q).
/* X = T,
Q = [].
*/
test(rename) :- reduit(rename, X ?= T, [f(X) ?= X], Q).
/* X = T,
Q = [f(T)?=T].
*/

%simplify
test(simplify) :- reduit(simplify, X ?= t, [], Q).
/* X = t,
Q = [].
*/
test(simplify) :- reduit(simplify, X ?= t, [f(X) ?= X], Q).
/* X = t,
Q = [f(t)?=t].
*/

%expand
test(expand) :- reduit(expand, X ?= f(t), [], Q).
/* X = f(t),
Q = [].
*/
test(expand) :- reduit(expand, X ?= f(t), [f(X) ?= X], Q).
/* X = f(t),
Q = [f(f(t))?=f(t)].
*/

%check
test(check, [fail]) :- reduit(check, X ?= f(t, Y, X, k), [f(X) ?= X], Q).
%Q = bottom.
test(check, [fail]) :- reduit(check, X ?= f(t, Y, X, k), [], Q).
%Q = bottom.

%orient
test(orient) :- reduit(orient, t ?= X, [f(X) ?= X], Q).
%Q = [X?=t, f(X)?=X].
test(orient) :- reduit(orient, t ?= X, [], Q).
%Q = [X?=t].

%clash
test(clash, [fail]) :- reduit(clash, f(t) ?= f(X, m), [], Q).
%Q = bottom.
test(clash, [fail]) :- reduit(clash, f(t) ?= g(X), [f(X) ?= X], Q).
%Q = bottom.
test(clash, [fail]) :- reduit(clash, f(t) ?= g(X), [], Q).
%Q = bottom.

%decompose
test(decompose):- reduit(decompose, f(t) ?= f(X), [f(X) ?= X], Q).
%Q = [t?=X, f(X)?=X].
test(decompose):- reduit(decompose, f(t, C, X) ?= f(X, k, Y), [], Q).
%Q = [t?=X, C?=k, X?=Y].
:- end_tests(reduit).

%% tests unifie
:- begin_tests(unifiebase_).
test(unifie) :- unifie([f(X,Y) ?= f(g(Z),h(a)), Z ?= f(Y)]).
/* trace_unif([f(X,Y) ?= f(g(Z),h(a)), Z ?= f(Y)], choix_premier).

system: [f(_396,_398)?=f(g(_402),h(a)),_402?=f(_398)]
decompose: f(_396,_398)?=f(g(_402),h(a))
system: [_396?=g(_402),_398?=h(a),_402?=f(_398)]
expand: _396?=g(_402)
system: [_398?=h(a),_402?=f(_398)]
expand: _398?=h(a)
system: [_402?=f(h(a))]
expand: _402?=f(h(a))
Unification terminee.Resultat: 

X = g(f(h(a))),
Y = h(a),
Z = f(h(a)).
*/

test(unifie, [fail]) :- unifie([f(X,Y) ?= f(g(Z),h(a)), Z ?= f(X)]).

:- end_tests(unifiebase_).

/* trace_unif([f(X,Y) ?= f(g(Z),h(a)), Z ?= f(X)], choix_premier).

system: [f(_8,_10)?=f(g(_14),h(a)),_14?=f(_8)]
decompose: f(_8,_10)?=f(g(_14),h(a))
system: [_8?=g(_14),_10?=h(a),_14?=f(_8)]
expand: _8?=g(_14)
system: [_10?=h(a),_14?=f(g(_14))]
expand: _10?=h(a)
system: [_14?=f(g(_14))]
check: _14?=f(g(_14))
system: [_14?=f(g(_14))]
false.
*/

:- begin_tests(unifie_).
test(unifie, [forall(member(STRATEGY ,[choix_premier, choix_pondere_1, choix_pondere_2]))]) :- 
    unifie([f(X,Y)?= f(g(Z), h(a)), Z ?= f(Y)], STRATEGY).
test(unifie, [forall(member(STRATEGY ,[choix_premier, choix_pondere_1, choix_pondere_2])), fail]) :- 
    unifie([f(X,Y)?= f(g(Z), h(a)), Z ?= f(Y), X ?= f(X)], STRATEGY).
test(unifie,[forall(member(STRATEGY,[choix_premier, choix_pondere_2]))]) :- 
   unifie([p(g(u,Z),X,Z) ?= p(X,g(Y,Z),b)],STRATEGY).

test(unifie,[forall(member(STRATEGY,[choix_pondere_1])), fail]) :- 
   unifie([p(g(u,Z),X,Z) ?= p(X,g(Y,Z),b)],STRATEGY).
test(unifie,[forall(member(STRATEGY ,[choix_premier, choix_pondere_1,choix_pondere_2])), fail]) :-
   unifie([p(X,f(X),h(f(X),X)) ?= p(Z,f(f(a)),h(f(g(a,Z)),v))],STRATEGY).


:- end_tests(unifie_).


/*?- trace_unif([p(g(u,Z),X,Z) ?= p(X,g(Y,Z),b)],choix_premier).

system: [p(g(u,_5086),_5092,_5086)?=p(_5092,g(_5098,_5086),b)]
decompose: p(g(u,_5086),_5092,_5086)?=p(_5092,g(_5098,_5086),b)
system: [g(u,_5086)?=_5092,_5092?=g(_5098,_5086),_5086?=b]
orient: g(u,_5086)?=_5092
system: [_5092?=g(u,_5086),_5092?=g(_5098,_5086),_5086?=b]
expand: _5092?=g(u,_5086)
system: [g(u,_5086)?=g(_5098,_5086),_5086?=b]
decompose: g(u,_5086)?=g(_5098,_5086)
system: [u?=_5098,_5086?=_5086,_5086?=b]
orient: u?=_5098
system: [_5098?=u,_5086?=_5086,_5086?=b]
simplify: _5098?=u
system: [_5086?=_5086,_5086?=b]
rename: _5086?=_5086
system: [_5086?=b]
simplify: _5086?=b
Unification terminee.Resultat: 

Z = b,
X = g(u, b),
Y = u.


?- trace_unif([p(X,f(X),h(f(x),x)) ?= p(Z,f(f(a)),h(f(g(a,Z)),v))],choix_premier).

system: [p(_9214,f(_9214),h(f(x),x))?=p(_9246,f(f(a)),h(f(g(a,_9246)),v))]
decompose: p(_9214,f(_9214),h(f(x),x))?=p(_9246,f(f(a)),h(f(g(a,_9246)),v))
system: [_9214?=_9246,f(_9214)?=f(f(a)),h(f(x),x)?=h(f(g(a,_9246)),v)]
rename: _9214?=_9246
system: [f(_9214)?=f(f(a)),h(f(x),x)?=h(f(g(a,_9214)),v)]
decompose: f(_9214)?=f(f(a))
system: [_9214?=f(a),h(f(x),x)?=h(f(g(a,_9214)),v)]
expand: _9214?=f(a)
system: [h(f(x),x)?=h(f(g(a,f(a))),v)]
decompose: h(f(x),x)?=h(f(g(a,f(a))),v)
system: [f(x)?=f(g(a,f(a))),x?=v]
decompose: f(x)?=f(g(a,f(a)))
system: [x?=g(a,f(a)),x?=v]

system: [x?=g(a,f(a)),x?=v]
false.

*/



