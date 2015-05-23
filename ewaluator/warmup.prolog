% let([define(id,(lm(x,x))),define(id2,(lm(x,x)))],id @ id2 @ (cons @ 7 @ (cons @ (plus @ (minus @ 8 @ 9) @ 4) @ nil)))

:-op(700, yfx, @).
:-dynamic evalCL/2.

% Ewaluacja podstawowych kombinatorów
evalCL(cI @ X,R):-!,evalCL(X,R).
evalCL(cK @ X @ _,R):-!,evalCL(X,R).
evalCL(cS @ X @ Y @ Z,R):-!,evalCL((X @ Z)@(Y @ Z),R).
evalCL(cB @ A @ B @ C,R):-!,evalCL(A @ (B @ C),R).
evalCL(cC @ A @ B @ C,R):-!,evalCL((A @ C) @ B,R).
% Ewaluacja arytmetyki
evalCL(plus @ A @ B,R):-!,evalCL(A,AR),evalCL(B,BR),R is AR+BR.
evalCL(minus @ A @ B,R):-!,evalCL(A,AR),evalCL(B,BR),R is AR-BR.
% Wyrażenie warunkowe
evalCL(if @ A @ B @ _,R):-evalCL(A,AR),0=\=AR,!,R=B.
evalCL(if @ A @ _ @ C,R):-evalCL(A,AR),0=:=AR,!,R=C.
% Listy (leniwe!)
evalCL(nil, []):-!.
evalCL(cons @ A @ B,R):-!,R=[A|B].
evalCL(fst @ A,HD):-!,evalCL(A,[HD|_]).
evalCL(snd @ A,TL):-!,evalCL(A,[_|TL]).
evalCL(isEmpty @ A,1):-evalCL(A,[]),!.
evalCL(isEmpty @ A,0):-evalCL(A,[_|_]),!.
evalCL(isEmpty @ _,_):-!,throw("isEmpty można aplikować tylko na liście").

%Inne kombinatory mogą być enkapsulowane np. let(x,f)...

evalCL(L @ R,X):-!,evalCL(L,LX), evalCLapp(L,LX,R,X).

evalCL(X,X).

evalCLapp(L,L,R,L @ R):-!.
evalCLapp(L,LX,R,S):-!,evalCL(LX @ R,S).

% Nazwy...
collectNames([],R):-!,R=[].
collectNames([define(ID,_)|TL],R):-!,collectNames(TL,Rest),R=[ID|Rest].

forget(X,[],R):-!,R=[].
forget(X,[HD|TL],R):-HD==X,!,forget(X,TL,R).
forget(X,[HD|TL],R):-!,forget(X,TL,RR),R=[HD|RR].

renameL(Prefix,Left @ Right,R):-!,renameL(Prefix,Left,LR),renameL(Prefix,Right,RR),R=(LR @ RR).
renameL(Prefix,lm(Name,Body),R):-!,renameL(Prefix,Body,BodyR),R=lm(Name,Body).
renameL(Prefix,let(Defs,Body),R):-!,collectNames(Defs,Names),renameLet(Prefix,let(Defs,Body),LetR),renameIds(Prefix,Names,LetR,R).
renameL(Prefix,Name,R):-!,R=Name.

% Tylko właściwe poddrzewa Let
renameLet(Prefix,let(Ids,Body),R):-!,renameLetIds(Prefix,Ids,IdsR),renameL([[]|Prefix],Body,BodyR),R=let(IdsR,BodyR).

renameLetIds(Prefix,[],R):-!,R=[].
renameLetIds(Prefix,[define(Id,IdImpl)|RestIds],R):-!,renameL([Id|Prefix],IdImpl,IdImplR),renameLetIds(Prefix,RestIds,RestIdsR),R=[define(Id,IdImplR)|RestIdsR].

% Zmień nazwy wolnych zmiennych z Names na [Name|Prefix] (nie rekurencyjne po let, rekurencyjne po już zmienionej strukturze)
renameIds(Prefix,Names,Left @ Right,R):-!,renameIds(Prefix,Names,Left,LeftR),renameIds(Prefix,Names,Right,RightR),R=(LeftR @ RightR).
renameIds(Prefix,Names,lm(Name,Body),R):-!,forget(Name,Names,NamesR),renameIds(Prefix,NamesR,Body,BodyR),R=lm(Name,BodyR).
renameIds(Prefix,Names,let(Defs,Body),R):-!,renameDefs(Prefix,Names,Defs,DefsR),renameIds(Prefix,Names,Body,BodyR),R=let(DefsR,BodyR).
renameIds(Prefix,Names,Name,R):-member(Name,Names),!,R=[Name|Prefix].
renameIds(Prefix,Names,Name,R):-!,R=Name.

% Zmień nazwy z definicji let (poddrzewa są już pozmieniane)
renameDefs(Prefix,Names,[],R):-!,R=[].
renameDefs(Prefix,Names,[define(Id,IdImpl)|Rest],R):-member(Id,Names),!,renameDefs(Prefix,Names,Rest,RestR),renameIds(Prefix,Names,IdImpl,IdImplR),R=[define([Id|Prefix],IdImplR)|RestR].
renameDefs(Prefix,Names,[define(Id,IdImpl)|Rest],R):-!,throw("Nieznany identyfikator").

% Nazwy mniejszych poddrzew są już unikalne
convertLtoCL(X @ Y, XC @ YC):-!,convertLtoCL(X,XC), convertLtoCL(Y,YC).
convertLtoCL(lm(X,Term),Result):-!,convertLtoCL(Term,TermC), prepareToApp(X,TermC,Result).
convertLtoCL(let([],X),Result):-!,convertLtoCL(X,Result). % Ciało let otrzymuje pustą liste jako identyfikator
convertLtoCL(let([define(ID, Body)|TL],X),Result):-!,convertLtoCL(Body,BodyCL), asserta((evalCL(ID,R):-!,evalCL(BodyCL,R))), convertLtoCL(let(TL,X),Result).
convertLtoCL(X,X):-!.

prepareToApp(X,Left @ Right,cS @ LeftR @ RightR):-haveLabel(X,Left), haveLabel(X,Right),!,prepareToApp(X,Left,LeftR), prepareToApp(X,Right,RightR).
prepareToApp(X,Left @ Right,cB @ Left @ RightR):-haveLabel(X,Right),!,prepareToApp(X,Right,RightR).
prepareToApp(X,Left @ Right,cC @ LeftR @ Right):-haveLabel(X,Left),!,prepareToApp(X,Left,LeftR).
prepareToApp(X,Left @ Right,cK @ (Left @ Right)):-!. % W zasadzie nie potrzebne
prepareToApp(X,lm(_,_),_):-!,throw("Abstrakcje powinny być już usunięte").
prepareToApp(X,Y,cI):-X==Y,!.
prepareToApp(X,Y,cK @ Y):-!.
%prepareToApp(X,Y,Y):-!. % Y powinien być kombinatorem

haveLabel(Label,A @ B):-haveLabel(Label,A).
haveLabel(Label,A @ B):-haveLabel(Label,B).
haveLabel(Label,Label).

%escapeVariables(appL(X,Y),appL(XE,YE)):-!,escapeVariables(X,XE),escapeVariables(Y,YE).
%escapeVariables(absL(X,Y),absL(X,YE)):-!,escapeVariables(Y,YE).
%escapeVariables(X,varL(X)):-!.
