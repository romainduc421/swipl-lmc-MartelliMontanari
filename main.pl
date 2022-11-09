% Definition de l'operateur "?=".
:- op(20,xfy,?=).

% echo(T): si le flag echo_on est positionné, echo(T) affiche le termeT
%          sinon, echo(T) réussit simplement en n'affichant rien.

echo(T) :- echo_on, !, write(T).
echo(_).


%%%%%% QUESTION 1

%%regle(E, R) : Determine la regle de transformation R qui s'applique a l'equation E.
%%----- Def des conditions sur les regles -----%

/*
 * Regle rename : renvoie true si X et T sont des variables.
 * E : equation donnee.
 * R : regle rename.
 */
regle(X?=T,rename):-
	var(X),
	var(T),
	!.
	 
/*
 * Regle simplify : renvoie true si X est une variable et T une
 * constante.
 * E : equation donnee.
 * R : regle simplify.
 */
regle(X?=T,simplify):- 
	var(X),
	const(T),
	!.

/*
 * Regle expand : renvoie true si X est une variable, T un terme
 * compose et si X n'est pas dans T.
 * E : equation donnee.
 * R : regle expand.
 */	
regle(X?=T,expand):-
	var(X),
	compound(T),
	occur_check(X,T),
	!.

/*
 * Regle check : renvoie true si X et T sont differents et si X est dans
 * T.
 * E : equation donnee.
 * R : regle check.
 */	
regle(X?=T,check):- 
	X\==T,
	\+occur_check(X,T),
	!.

/*
 * Regle orient : renvoie true si T n'est pas une variable et si X en
 * est une.
 * E : equation donnee.
 * R : regle orient.
 */
regle(T?=X,orient):-
	nonvar(T),
	var(X),
	!.

/*
 * Regle decompose : renvoie true si X et T sont des termes composes et
 * s'ils ont le meme nombre d'arguments et le meme nom.
 * E : equation donnee.
 * R : regle decompose.
 */	
regle(T1?=T2,decompose):-
	\+regle(T1?=T2,expand),
	!,
	functor(T1,F1,A1),
	functor(T2,F2,A2),
	F1==F2,
	A1==A2,
	!.

/*
 * Regle clash : renvoie true si X et T sont des termes composes et
 * s'ils n'ont pas le meme nombre d'arguments.
 * E : equation donnee.
 * R : regle clash.
 */
regle(T1?=T2,clash):-
	\+(functor(T1,F,A)=functor(T2,F,A)),
	!.

% occur_check(V,T): teste si la variable V apparait dans le terme T
occur_check(V,T):-    
	var(T),
	!,
	V \== T,
	!.
	
occur_check(V,T):-
	T =.. [_|R],
	occur_check_list(V,R).

occur_check_list(_V,[]):-!.

occur_check_list(V,[A|R]):-
	occur_check(V,A),
	occur_check_list(V,R),
	!.
