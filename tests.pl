%test rules
%rename

?- regle(X ?= T, R).
R = rename.

?- regle(X ?= a, rename).
false.

?- regle(X ?= f(a), rename).
false.

?- regle(X ?= f(X), rename).
false.

%simplify

?- regle(X ?=t, R).
R = simplify.

?- regle(X?=a, simplify).
true.

?- regle(X?=f(a), simplify).
false.

?- regle(X ?= f(X), simplify).
false.

%check

?- regle(X?=f(X),R).
R = check.

?- regle(X ?= a, check).
false.

?- regle(X ?= f(a), check).
false.

?- regle(X ?= f(X), check).
true.

%orient

?- regle(t ?= X, R).
R = orient.

?- regle(t ?= X, orient).
true.

?- regle(X ?= f(a), orient).
false.

?- regle(X ?= a, orient).
false.

%decompose

?- regle(f(t) ?= f(X), R).
R = decompose.

?- regle(f(X) ?= X, decompose).
false.

?- regle(f(X) ?= f(X, Y), decompose).
false.

?- regle(f(X) ?= f(a), decompose).
true.

?- regle(f(X) ?= g(Y), decompose).
false.

%clash

?- regle(f(t) ?= g(X, a), R).
R = clash.

?- regle(f(X) ?= X, clash).
false.

?- regle(f(X) ?= f(X, Y), clash).
true.

?- regle(f(X) ?= f(a), clash).
false.

?- regle(f(X) ?= g(Y), clash).
true.

%expand
?- regle(X?=f(a,b),expand).
true.

?- regle(X?=f(a,b,X),expand).
false.

?- regle(X?=f(f(a),b,X),expand).
false.

?- regle(X?=f(f(X,b,a),b,a),expand).
false.

?- regle(X?=f(f(Y,b,a),b,a),expand).
true.

?- regle(X?=f(g(X,b,a),b,a),expand).
false.

?- regle(X?=f(g(h(X),b,a),b,a),expand).
false.

?- regle(X?=f(g(h(Y),b,a),b,a),expand).
true.

%% tests reduit
%rename
?- reduit(rename, X ?= T, [], Q).
X = T,
Q = [].

?- reduit(rename, X ?= T, [f(X) ?= X], Q).
X = T,
Q = [f(T)?=T].

%simplify
?- reduit(simplify, X ?= t, [], Q).
X = t,
Q = [].

?- reduit(simplify, X ?= t, [f(X) ?= X], Q).
X = t,
Q = [f(t)?=t].

%expand
?- reduit(expand, X ?= f(t), [], Q).
X = f(t),
Q = [].

?- reduit(expand, X ?= f(t), [f(X) ?= X], Q).
X = f(t),
Q = [f(f(t))?=f(t)].

%check
?- reduit(check, X ?= f(t, Y, X, k), [f(X) ?= X], Q).
Q = bottom.

?- reduit(check, X ?= f(t, Y, X, k), [], Q).
Q = bottom.

%orient
?- reduit(orient, t ?= X, [f(X) ?= X], Q).
Q = [t?=X, f(X)?=X].

?- reduit(orient, t ?= X, [], Q).
Q = [t?=X].

%clash
?- reduit(clash, f(t) ?= f(X, m), [], Q).
Q = bottom.

?- reduit(clash, f(t) ?= g(X), [f(X) ?= X], Q).
Q = bottom.

?- reduit(clash, f(t) ?= g(X), [], Q).
Q = bottom.

%decompose
?- reduit(decompose, f(t) ?= f(X), [f(X) ?= X], Q).
Q = [t?=X, f(X)?=X].

?- reduit(decompose, f(t, C, X) ?= f(X, k, Y), [], Q).
Q = [t?=X, C?=k, X?=Y].



