//version 19-07-11
//agregue funcion MyExtendBasis para corregir problemas con 
//ExtendBasis.
//cambios en la funcion RiemannHurwitz para encontrar posibles signaturas con genero abajo >0

//version 25-08-09

forward poly, Symplectic_Form, BetterBasis, RH, SymplecticMatrix;

cota:=2;  //decreasing this number will make things run faster but likelihood of lots of zeroes in the representation goes down.

intrinsic polygon(group::GrpPerm,generators::[GrpPermElt])->Rec
    {returns a record containing 
loops:  Sequence of closed paths forming a preliminary basis for the homology

Ji:  Intersection matrix of the original basis of curves
P:  integer matrix which represents a change of basis so that the intersection matrix becomes the standard J
x:  Sequence of matrices corresponding to the symplectic images of the generators used.
    Example:
    r:=polygon(Sym(4),[Sym(4)|(1, 4, 2, 3),(1, 3, 4, 2),(1, 4, 2)])}
    require #generators ge 2:"You need at least 2 generators (or 3 if their product is 1)";
    require sub<group|generators> eq group: "The generators don´t generate the given group"; 
    return poly(group,generators);
end intrinsic;

intrinsic MyExtendBasis(l::[ModTupFldElt],V::ModTupFld)->SeqEnum
    {}
    r:=l;
    b:=Basis(V);
    for v in b do
        W:=sub<V|r>;
        if not v in W then r:=Append(r,v); end if;
    end for;
    return r;
end intrinsic;

intrinsic polygon(group::GrpPerm,signature::[RngIntElt])->Rec
    {returns a record containing ...
    Example:
    r:=polygon(Sym(4),[4,4,3])}
    require #signature ge 3:"You need at least 3 marks";
    l:=FindGenerators(group,signature);
    if l eq [] then error "The given group can not mark in that way"; end if;
    return poly(group,l[1]);
end intrinsic;

intrinsic polygon(group::GrpPC,signature::[RngIntElt])->Rec
    {returns a record containing ...
    Example:
    r:=polygon(Sym(4),[4,4,3])}
    require #signature ge 3:"You need at least 3 marks";
    l:=FindGenerators(group,signature);
    if l eq [] then error "The given group can not mark in that way"; end if;
    return poly(group,l[1]);
end intrinsic;

intrinsic Inverse(g::GrpPCElt)->GrpPCElt
    {}
    return g^(-1);
end intrinsic;

poly:=function(grupo,generadores)
    if &*generadores eq grupo!1 then Remove(~generadores,#generadores); end if;
    if #generadores lt 2 then error "You need at least 2 generators (or 3 if their product is 1)"; end if;
    ttt:=Cputime();
    //The edge-format will be [left face, conection, right face].  
    //Faces are numbered according to their position in the list caras.
    og:=Order(grupo);
    gens:=[grupo|];
    invgens:=[];
    g1:=generadores[1];
    //The first generator in the given list will form the faces around the center.
    caras:=[grupo|g1^k:k in [0..Order(g1)-1]]; 
    //Expands the list of generators to include their inverses.  It also creates a second list containing the positions of the inverses of the generators.
    k:=1;
    for i in generadores do  
        if Order(i) eq 2 then Append(~gens,i); Append(~invgens,k); k:=k+1; end if;
        if Order(i) gt 2 then Append(~gens,i);Append(~gens,Inverse(i)); Append(~invgens,k+1); Append(~invgens,k); k:=k+2; end if;
    end for;
    ng:=#gens;
    //given an edge, finds the same edge with opposite orientation.
    Reverso:=function(x) 
        return [x[3],invgens[x[2]],x[1]];
    end function;

    //conexiones will be a list containing a list for each face.  
    //Each of these lists in turn contains an entry for each of its edges
    //which is 0 if it is free and n if it is connected to the n-th face.
    conexiones:=[[0:i in [1..ng]]:j in [1..og]];
    //Establishes the connections between the central faces of the polygon.
    for c in [1..#caras] do
        c2:=Position(caras,caras[c]*gens[1]);
        g2:=invgens[1];
        conexiones[c][1]:=c2;
        conexiones[c2][g2]:=c; end for; 
    n:=#caras;
    
    //attaches further faces to the polygon until the size of the group is reached.
    while n lt og do;
    //print caras;
    for g in [1..ng] do 
      //print n;
      for c in [1..n] do
         cn:=caras[c]*gens[g];
         if not cn in caras then
              Append(~caras,cn);
              //print caras[c],gens[g],cn,0;
              c2:=#caras;
        g2:=invgens[g];
        conexiones[c][g]:=c2;
        conexiones[c2][g2]:=c;
        end if;     
      end for;
      //n:=#caras;
    end for;
    n:=#caras;
    end while;
    lf:=caras[og];
    
    g:=g2 mod ng +1; //The first free edge of the first face of the border. (the face attached last)
    preborde:=[];          
    listo:=0;
    actual:=[og,0,0];
    repeat
        while conexiones[actual[1]][g] eq 0 do
            actual[2]:=g;
            actual[3]:=Position(caras,caras[actual[1]]*gens[g]);
            Append(~preborde,actual);
            g:=g mod ng +1; 
        end while;
        actual[1]:=Position(caras,caras[actual[1]]*gens[g]);
        g:=invgens[g] mod ng +1;
        actual[2]:=g;
        actual[3]:=Position(caras,caras[actual[1]]*gens[g]); 
        if actual eq preborde[1] then listo:=1; end if;//verifica si ya volvio al comienzo del preborde 
    until listo eq 1;

    //this preborder may contain some consecutive edges which are actually the same edge with opposite orientations. 
    //in that case they should not form part of the border and are removed.
    //the removal process may take several passes.
    listo:=0;
    borde:=preborde;
    while listo eq 0 do
        i:=1;
        while i eq 1 do
            n:=#preborde;
            if preborde[1] eq Reverso(preborde[n]) then 
            Remove(~preborde,n); Remove(~preborde,1); 
            else i:=2; 
            end if;
        end while;
        while i lt #preborde do
              if preborde[i] eq Reverso(preborde[i+1]) then 
                Remove(~preborde,i); Remove(~preborde,i); 
                if i gt 1 then i:=i-1; end if;
            else i:=i+1; 
            end if;
        end while;
        if #borde eq #preborde then listo:=1; end if;
        borde:=preborde;
    end while;
    nb:=#borde;
    na:=nb div 2;
    //print borde;
    
    bordenumerado:=[0:x in borde];
    i:=1;
    while exists(p){i:i in [1..nb]|bordenumerado[i] eq 0} do
        bordenumerado[p]:=i;
        p1:=Position(borde, borde[p],p+1);
        if p1 eq 0 then p1:=Position(borde, Reverso(borde[p]),p+1); bordenumerado[p1]:=-i;
        else bordenumerado[p1]:=i; end if;
        i:=i+1;
    end while;
    //numera los vertices del borde cuidando de dar el mismo numero a vertices identificados
    vertices:=[0: x in borde];
    i:=1;
    while exists(p){i:i in [1..nb]|vertices[i] eq 0} do //looks for the first vertex with no label
        vertices[p]:=i;
        n:=Position(bordenumerado,-bordenumerado[p]) mod nb +1;  //it finds the position of the edge identified with the current one
                                    // and considers the next edge along the border.
                                    // the beginning vertex of that edge will be identified with the current vertex.
        while n ne p do
            vertices[n]:=i;
            n:=Position(bordenumerado,-bordenumerado[n]) mod nb +1;
        end while;
        i:=i+1;
    end while;
    nv:=i-1; //Total number of different vertices on the border
    
    giro:=function(x) //dada una arista x gira en sentido positivo alrededor de la cola y devuelve la aristas que encuentra.
        g:=(x[2]-2) mod ng +1;
        return [Position(caras,caras[x[1]]*gens[g]),invgens[g],x[1]]; 
    end function;    

    girohorario:=function(x) //dada una arista gira en sentido horario alrededor de la cola y devuelve la aristas que encuentra.
        g:=invgens[x[2]] mod  ng +1;
        return [x[3],g,Position(caras,caras[x[3]]*gens[g])]; 
    end function;    


    comienzo:=function(x) 
/*    Dada una arista, verifica si el vértice inicial está en el borde y en tal caso entrega su posición.
    En caso contrario devuelve 0
*/
        j:=x;
        repeat
            if j in borde then return Position(borde,j); end if;
            j:=girohorario(j);
        until j eq x;
        return 0;
    end function;
        
    final:=function(x)
        if x in borde then return Position(borde,x) mod nb +1; end if;
        return comienzo(Reverso(x));
    end function;

    

    cocomenzantes:=function(i) 
/*    Dada una aristas i devuelve una lista con las otras aristas que salen del mismo vertice en orden positivo. 
*/
        rr:=[];    
        j:=giro(i);
        while j ne i do 
            Append(~rr,j);
            j:=giro(j);
        end while;
        return rr;
    end function;

    coterminales:=function(i)
        return [Reverso(j):j in cocomenzantes(Reverso(i))];
    end function;

    //crea una lista de aristas del borde sin duplicacion y fabrica la matriz de ecuaciones 
    //que debe satisfacer una curva (lista de aristas) para ser un ciclo.  
    //Esto permitira obtener una base para la homologia.
    aristas:=[];
    m:=ZeroMatrix(IntegerRing(),nv,na);
    for i in [1..nb] do
        if not Reverso(borde[i]) in aristas then 
            Append(~aristas,borde[i]);
            j:=#aristas;
            m[vertices[i]][j]-:=1;
            m[vertices[i+1]][j]+:=1;
        end if;
    end for;
    
    //matriz cuyas filas representan los ciclos en terminos de las aristas.
    homologia:=Nullspace(Transpose(m));
    genero:=Dimension(homologia) div 2;
    ciclos:=Matrix(Basis(homologia));

    accion:=function(g,i) // accion de g la arista i.
        return [Position(caras,g*caras[i[1]]),i[2],Position(caras,g*caras[i[3]])];
    end function;

    
    
    //Dada una lista de aristas, devuelve los vertices iniciales de cada una
    ver:=function(a)
        return [vertices[Position(borde,i)]:i in a];
    end function;


    camino:=function(a)  //a partir de la matriz de ciclos obtiene la a-esima curva de la base 
                //como suma de aristas cambiando orientacion para evitar signos -
                //y ordenando las aristas para que el vertice final de una corresponda con
                // el vertice inicial de la siguiente.
        rr:=[];
        rvo:=[];
        for i in [1..na] do
            if a[i] eq 1 then Append(~rr,aristas[i]); end if;
            if a[i] eq -1 then Append(~rr,Reverso(aristas[i])); end if;
        end for;
        rv:=[[vertices[Position(borde,i)],vertices[Position(borde,i)mod nb +1]]:i in rr];
        rvo[1]:=rv[1];
        for i in [1..#rv-1] do
             for j in [1..#rv] do
                if rvo[i][2] eq rv[j][1] then Append(~rvo,rv[j]); end if;
            end for;
        end for;
        ro:=[rr[Position(rv,x)]:x in rvo];
        return ro;
    end function;

    caminos:=[camino(ciclos[i]):i in [1..NumberOfRows(ciclos)]];

    
    cameq:=function(x)
/*    Dado un  camino cerrado x como lista de aristas encuentra otro equivalente con aristas del borde.
    Se asume que x pasa por al menos un vértice del borde.
        
*/
        c:=x;
        rr:=[];
        //establece el inicio del la representacion del camino cerrado en un punto del borde
        while comienzo(c[1]) eq 0 do
            Append(~c,c[1]);
            Remove(~c,1);
        end while;
        while c ne [] do
             ai:=comienzo(c[1]);
            while final(c[1]) eq 0 do
                Remove(~c,1);
            end while;
             af:=final(c[1]);
            Remove(~c,1);
            i:=ai;
            while i ne af do
                Append(~rr,borde[i]);
                i:=i mod nb +1;
            end while;
        end while;
        l:=[0:i in [1..na]];
        for i in rr do 
            if i in aristas then l[Position(aristas,i)]:=l[Position(aristas,i)]+1; end if;
            if Reverso(i) in aristas then 
                l[Position(aristas,Reverso(i))]:=l[Position(aristas,Reverso(i))]-1; end if;
        end for;
        return l;
    end function;
    
    
    interseccion:=function(a,b) //encuentra el numero de interseccion entre las curvas a y b.  
        rr:=0;
        for i in a do
            if not (i in b or Reverso(i) in b) then 
                l:=cocomenzantes(i);
                for j in l do
                    if j in b then rr:=rr+1/2; break; end if;
                    if Reverso(j) in b then rr:=rr-1/2; break; end if;
                end for;
                l:=coterminales(i);
                for j in l do
                    if j in b then rr:=rr+1/2; break; end if;
                    if Reverso(j) in b then rr:=rr-1/2; break; end if;
                end for;
            end if;
        end for;
        return rr;
    end function;

    matrizdeinterseccion:=Matrix(IntegerRing(),[[interseccion(i,j):j in caminos]:i in caminos]);

    J,P:=Symplectic_Form(matrizdeinterseccion); //P is the change of basis which turns the intersection matrix into canonical form.
    representacionsimplectica:=function(g,P)
        l:=[cameq([accion(g,i):i in c]):c in caminos];
        return P^-1*Transpose(Matrix([Solution(ciclos,Vector(l[i])):i in [1..2*genero]]))*P;    
    end function;

    x:=[representacionsimplectica(g,P):g in generadores];

    y:=MatrixGroup<2*genero,IntegerRing()|x>;
    y:=[Matrix(IntegerRing(),i):i in y];
    Q:=1;
 //   Q:=BetterBasis(y); Debo cambiarlo por Q:=1
    P:=P*Q;
    x:=[representacionsimplectica(g,P):g in generadores];
//verifica que las matrices encontradas son simplecticas    
    for i in x do
        if not ZeroMatrix(IntegerRing(),2*genero,2*genero) eq Transpose(i)*J*i-J then 
            print("error en la verificacion");
        end if;
    end for;
//verifica que el grupo generado por las matrices encontradas es isomorfo al grupo original
    if not IdentifyGroup(grupo) eq IdentifyGroup(MatrixGroup<2*genero,IntegerRing()|x>) then 
            print("error en la verificacion");
        end if;
    print "The computation took",Cputime(ttt), "segundos";
/*
    formato:=recformat<ng:RngIntElt, generadores:SeqEnum, grupo:GrpPerm, caras:SeqEnum, conexiones:SeqEnum, vertices:SeqEnum, nb:RngIntElt, na:RngIntElt, nv:RngIntElt, ciclos:ModMatRngElt, aristas:SeqEnum, caminos:SeqEnum, Ji:AlgMatElt, genero:RngIntElt, x:SeqEnum, j:AlgMatElt, borde:SeqEnum, preborde:SeqEnum, giro:UserProgram,P:AlgMatElt,z0:AlgMatElt,zi:SeqEnum,loops:SeqEnum>;
    r:=rec<formato|grupo:=grupo, generadores:=generadores, caras:=caras, x:=x, j:=J, Ji:=matrizdeinterseccion, vertices:=vertices, ciclos:=ciclos, borde:=borde, giro:=giro,conexiones:=conexiones,preborde:=preborde>;
*/
    formatoc:=recformat<Ji:AlgMatElt, x:SeqEnum, P:AlgMatElt, loops:SeqEnum, edges:SeqEnum,z0:AlgMatElt,zi:SeqEnum,vertices:SeqEnum,conexiones:SeqEnum>;
    caminosnumerados:=[[bordenumerado[Position(borde,i)]:i in j]:j in caminos];
    rc:=rec<formatoc|Ji:=matrizdeinterseccion, x:=x,P:=P,loops:=caminosnumerados,edges:=bordenumerado,vertices:=vertices,conexiones:=conexiones>;
    print "The answer is a record containing the following fields:";
    print "edges: Sequence of numbers labeling the edges of the border. Edge -3 is identified with edge 3.";
    print "vertices: Sequence of numbers labeling the distinct vertices of the border.  The first vertex corresponds to the beginning of the first edge.";
    print "loops:  sequence of closed paths forming a preliminary basis for the homology";
    print "Ji:  Intersection matrix of the original basis of curves";
    print "P:  integer matrix which represents a change of basis so that the intersection matrix becomes the standard J";
    print "x:  Sequence of matrices corresponding to the symplectic images of the generators used.";
    if Q ne 1 then 
        L:=MoebiusInvariant(x);
        R:=L`R;
        I:=L`I;
        z:=L`Z;
        n,l:=Dimension(I);
        J:=[R.i:i in l];
        S,f:=R/(Ideal(J)+I);
        z0:=Matrix(RationalField(),genero,genero,f(Eltseq(z)));
        zi:=[];
        for i in [1..#J] do
            J[i]-:=1;
            S,f:=R/(Ideal(J)+I);
            m:=Matrix(RationalField(),genero,genero,f(Eltseq(z)));
            dm:=LCM([Denominator(i):i in Eltseq(m)]);
            Append(~zi,dm*m);
            J[i]+:=1;
        end for;
        rc`z0:=z0;
        rc`zi:=zi;
        print "";
        print "We succeeded in finding Riemann matrices invariant under the action of x.";
        print "Matrices are given by Z=z0+alpha1*z1+alpha2*z2+... where z0 and zi are fields in the output";
    end if;
    print "";
    printf "The border starts at the face corresponding to the group element ";
    print lf;
    print "The group elements used as generators are ";
    print generadores;
return rc;
end function;





intrinsic MoebiusInvariant(y::[AlgMatElt])->Rec
    {returns a record containing a polynomial ring R, and ideal I and a matrix Z with coefficients in R whose image in R/I is invariant under Moebius action by the given matrices}
    x:=[g:g in MatrixGroup<NumberOfRows(y[1]),IntegerRing()|y>];
    g:=NumberOfRows(x[1])div 2;
    J:=ZeroMatrix(IntegerRing(),2*g,2*g);
    for i in [1..g] do J[i+g][i]:=-1; J[i][i+g]:=1;end for;
    a:=[Submatrix(m,1,1,g,g):m in x];
    b:=[Submatrix(m,1,g+1,g,g):m in x];
    c:=[Submatrix(m,g+1,1,g,g):m in x];
    d:=[Submatrix(m,g+1,g+1,g,g):m in x];
    Q:=RationalField();
    R:=PolynomialRing(Q,(g*(g+1))div 2);
    Z:=SymmetricMatrix(R,[R.i:i in [1..(g*(g+1))div 2]]);
    l:=[(a[i]*Z+b[i])-Z*(c[i]*Z+d[i]):i in [1..#x]];
    ecs:=[];
    for i in l do
        ecs:=ecs cat Eltseq(i);
    end for;
    I:=Ideal(ecs);
    Groebner(I);
    form:=recformat<R:RngMPol,I:RngMPol,Z:AlgMatElt>;
return rec<form|R:=R,I:=I,Z:=Z>;

end intrinsic;

intrinsic MoebiusInvariantAni(y::[AlgMatElt])->Rec
    {returns a record containing a polynomial ring R, and ideal I and a matrix Z with coefficients in R whose image in R/I is invariant under Moebius action by the given matrices}
    x:=[g:g in MatrixGroup<NumberOfRows(y[1]),IntegerRing()|y>];
    g:=NumberOfRows(x[1])div 2;
    J:=ZeroMatrix(IntegerRing(),2*g,2*g);
    for i in [1..g] do J[i+g][i]:=-1; J[i][i+g]:=1;end for;
    a:=[Submatrix(m,1,1,g,g):m in x];
    b:=[Submatrix(m,1,g+1,g,g):m in x];
    c:=[Submatrix(m,g+1,1,g,g):m in x];
    d:=[Submatrix(m,g+1,g+1,g,g):m in x];
    Q:=RationalField();
    R:=PolynomialRing(Q,(g*(g+1))div 2);
    Z:=SymmetricMatrix(R,[R.i:i in [1..(g*(g+1))div 2]]);
    l:=[(Z*d[i]+b[i])-(Z*c[i]+a[i])*Z:i in [1..#x]];
    ecs:=[];
    for i in l do
        ecs:=ecs cat Eltseq(i);
    end for;
    I:=Ideal(ecs);
    Groebner(I);
    form:=recformat<R:RngMPol,I:RngMPol,Z:AlgMatElt>;
return rec<form|R:=R,I:=I,Z:=Z>;

end intrinsic;

// Aqui empieza la nueva (G::GrpPerm,g::RngIntElt) AlgMatElt

intrinsic MoebiusInvariantDZ(td::[RngIntElt], y::[AlgMatElt])->Rec
    {returns a record containing a polynomial ring R, and ideal I and a matrix Z with coefficients in R whose image in R/I is invariant under Moebius action by the given matrices}
    x:=[g:g in MatrixGroup<NumberOfRows(y[1]),IntegerRing()|y>];
    g:=NumberOfRows(x[1])div 2;
    J:=ZeroMatrix(IntegerRing(),2*g,2*g);
    for i in [1..g] do J[i+g][i]:=-1; J[i][i+g]:=1; end for;
    D:=DiagonalMatrix(td);
    tdi:=[j^-1: j in td];
    Di:=DiagonalMatrix(tdi);
    ao:=[Submatrix(m,1,1,g,g):m in x];
    a:=[D*j*Di: j in ao];
    bo:=[Submatrix(m,1,g+1,g,g):m in x];
    b:=[D*j: j in bo];
    co:=[Submatrix(m,g+1,1,g,g):m in x];
    c:=[j*Di: j in co];
    d:=[Submatrix(m,g+1,g+1,g,g):m in x];
    Q:=RationalField();
    R:=PolynomialRing(Q,(g*(g+1))div 2);
    Z:=SymmetricMatrix(R,[R.i:i in [1..(g*(g+1))div 2]]);
    l:=[(Z*d[i]+b[i])-(Z*c[i]+a[i])*Z:i in [1..#x]];
    ecs:=[];
    for i in l do
        ecs:=ecs cat Eltseq(i);
    end for;
    I:=Ideal(ecs);
    Groebner(I);
    form:=recformat<R:RngMPol,I:RngMPol,Z:AlgMatElt>;
return rec<form|R:=R,I:=I,Z:=Z>;

end intrinsic;
// hasta aquí cambie el 2021 para Z con D


// Aqui empieza otra nueva (G::GrpPerm,g::RngIntElt) AlgMatElt 


// hasta aqui cambie el 2021 para consolidar Z con D y E




//Not currently in use
sonconjugadas:=function(x,y)
    g:=NumberOfRows(x[1])div 2;
    J:=SymplecticMatrix(g);
    R:=PolynomialRing(RationalField(),4*g*g);
    z:=Matrix(R,2*g,2*g,[R.i:i in [1..4*g*g]]);
    l1:=Transpose(z)*J*z-J;
    l:=[x[i]*z-z*y[i]:i in [1..#x]];
    ecs:=Eltseq(l1);
    for i in l do
        ecs:=ecs cat Eltseq(i);
    end for;
    I:=Ideal(ecs);
    Groebner(I);
    return R,I,z;
end function;

SymplecticMatrix:=function(g)
    J:=ZeroMatrix(IntegerRing(),2*g,2*g);
    for i in [1..g] do J[i+g][i]:=-1; J[i][i+g]:=1;end for;
    return J;
end function;

descparcial:=function(x,n,m,j) 
//comienza la descomposicion de x como suma de n fracciones 1/i cuyos denominadores dividen a m y son al menos j (se asume j mayor o igual a 2.
//entrega un par [1/i,x-1/i].
    k:=Floor(n/x);
    if n eq 1 then if x eq 1/k then return [[k]]; else return []; end if; end if;
    k0:=Maximum(Floor(1/x+1),Floor(j));
    d:=[i:i in [k0..k]|(m mod i) eq 0];
    l:=[[i,x-1/i]:i in d];
    return l;
end function;

forward desctotal;

desctotal:=function(x,n,m,j)
    if n eq 1 then return descparcial(x,n,m,j); end if;
    l:=descparcial(x,n,m,j);
    r:=[];
    for i in l do
        t1:=desctotal(i[2],n-1,m,i[1]);
        t2:=Remove(i,2);
        s:=[t2 cat k: k in t1];
        r:=r cat s;
    end for;
    return r;
end function;

intrinsic desc(x::FldRatElt,n::RngIntElt,m::RngIntElt)->[]
    {Comentario   }
    return [Reverse([Integers()!j:j in i]): i in desctotal(x,n,m,2)];
end intrinsic;


intrinsic RiemannHurwitz0(n::RngIntElt,g::RngIntElt)->[]
    {Given a group order n and a genus g gives a list of all compatible signatures.
    This does not verify existence of a group with that signature.
    If you have a specific group, try SuggestSignatures(G,g) instead.}
    k:=Floor((g+n-1)*4/n);
    k0:=(g+n-1)*2/n;
    if k0 eq Floor(k0) then k0:=k0+1; end if;
    k0:=Floor(k0);
    k0:=Max(k0,3);
    r:=[];
    for t in [k0..k] do
        c:=t-2-2*(g-1)/n;
        d:=desc(c,t,n);
        r:=r cat d;
    end for;
return r;
end intrinsic;

intrinsic RiemannHurwitz(n::RngIntElt,g::RngIntElt)->[]
    {Given a group order n and a genus g gives a list of all compatible signatures.
    This does not verify existence of a group with that signature.
    If you have a specific group, try SuggestSignatures(G,g) instead.}
    maxgamma:=Floor((g-1)/n+1);
    r:=[];
    for gamma in [0..maxgamma] do
        k:=Floor((g-n*(gamma-1)-1)*4/n);
        k0:=(g-n*(gamma-1)-1)*2/n;
        if k0 eq Floor(k0) then k0:=k0+1; end if;
        k0:=Floor(k0);
        //k0:=Max(k0,3);
        rp:=[];
        for t in [k0..k] do
            c:=t+2*(gamma-1)-2*(g-1)/n;
            d:=desc(c,t,n);
            rp:=rp cat d;
        end for;
        r:=r cat [[*gamma,rp*]];
    end for;
return r;
end intrinsic;


intrinsic RH(G::GrpPerm,g::RngIntElt)->[]
    {Given a group G and a genus g it looks for possible actions of G on a curve of genus g and returns a list of records with the following attributes:
     signature, gens, dimB.  Each record corresponds to a possible action.  No claim is made of whether these actions are non-equivalent}
    r:=RiemannHurwitz0(#G,g);
    s:=[FindGenerators(G,i):i in r];
    R:=[];
    S:=[];
    for i in r do 
        s:=FindGenerators(G,i);
        S:=S cat s;
        R:=R cat [i:j in s];
    end for;
    p1:=PermutationCharacter(G,sub<G|1>);
    Y:=[2*PrincipalCharacter(G)-2*p1+&+[p1-PermutationCharacter(G,sub<G|i>):i in x]:x in S];
    ct:=CharacterTable(G);
    cd:=[x[1]:x in ct];
    B:=[[-x[1]+1/2*&+[x[1]-InnerProduct(x,PermutationCharacter(G,sub<G|i>)):i in sol]:x in ct]:sol in S];
    Yd:=[[IntegerRing()!k: k in Decomposition(ct,i)]:i in Y];
    form:=recformat<signature:SeqEnum,gens:SeqEnum,dimB:SeqEnum>;
    print ct;
    return [rec<form|signature:=R[i],gens:=S[i],dimB:=B[i]>:i in [1..#R]];
end intrinsic;



Existence2:=function(g,l) //here l is expected to be a list of specific subsets of the group from which to take the generators
    p:=[[k:k in x]:x in CartesianProduct(l)];

    for i in p do
        if &*i eq g!1 and sub<g|i> eq g then return i; end if;
    end for;
return [];
end function;

intrinsic FindGenerators(G::GrpPerm,l::[RngIntElt])->[] //here l is expected to be a list of orders for the generators
    {Given a group G and a signature l (given as a list of integers) it finds possible generator sets for G}
    cc:=ConjugacyClasses(G);
    s:=[[i[3]:i in cc| i[1] eq j]:j in l];
    p:=[[k:k in x]:x in CartesianProduct(s)];
    sols:=[];
    for i in [1..#p] do
        L:=[[j: j in p[i][n]^G|Order(j) eq l[n]]:n in [1..#l]];
        sol:=Existence2(G,L);
        if sol ne [] then Append(~sols,sol); end if;
    end for;
return sols;
end intrinsic;

intrinsic FindGenerators2(G::GrpPerm,l::[RngIntElt])->[] //here l is expected to be a list of orders for the generators
    {Given a group G and a signature l (given as a list of integers) it finds possible generator sets for G}
    cc:=ConjugacyClasses(G);
    s:=[[i[3]:i in cc| i[1] eq j]:j in l];
    p:=[[k:k in x]:x in CartesianProduct(s)];
    sols:=[];
    for i in [1..#p] do
        L:=[[j: j in p[i][n]^G|Order(j) eq l[n]]:n in [1..#l]];
        L[1]:=[L[1][1]];
        sol:=Existence2(G,L);
        if sol ne [] then Append(~sols,sol); break; end if;
    end for;
return sols;
end intrinsic;

intrinsic FindGenerators(G::GrpPC,l::[RngIntElt])->[] //here l is expected to be a list of orders for the generators
    {Given a group G and a signature l (given as a list of integers) it finds possible generator sets for G}
    cc:=ConjugacyClasses(G);
    s:=[[i[3]:i in cc| i[1] eq j]:j in l];
    p:=[[k:k in x]:x in CartesianProduct(s)];
    sols:=[];
    for i in [1..#p] do
        L:=[[j: j in p[i][n]^G|Order(j) eq l[n]]:n in [1..#l]];
        L[1]:=[L[1][1]];
        sol:=Existence2(G,L);
        if sol ne [] then Append(~sols,sol); break; end if;
    end for;
return sols;
end intrinsic;


intrinsic SuggestSignatures(G::GrpPerm,g::RngIntElt)->[]
    {List of possible signatures for G acting on a surface of genus g}
    r:=RiemannHurwitz0(#G,g);
    s:=[FindGenerators(G,i):i in r];
    r:=[r[i]:i in [1..#r]|s[i] ne []];
    return r;
end intrinsic;


//M is expected to be an antisymmetric matrix representing a symplectic form
//As a result we get a change of basis matrix P such that P^tMP is the standard symplectic matrix
Symplectic_Form:=function(M)
    g:=NumberOfRows(M) div 2;  
    m:=IdentityMatrix(IntegerRing(),2*g);

    for i in [1..g] do
        
        l:=Eltseq(RowSubmatrix(m,2*i-1,1)*M*Transpose(RowSubmatrix(m,2*i,2*g-2*i+1)));
            while not 1 in l do
                for j in [2*i..2*g] do
                    if l[j-2*i+1] lt 0 then m[j]:=-m[j]; end if;
                end for;
                l:=Eltseq(RowSubmatrix(m,2*i-1,1)*M*Transpose(RowSubmatrix(m,2*i,2*g-2*i+1)));
                n:=Min([i : i in l|i ne 0]);
                n:=Position(l,n)+2*i-1;
                for j in [2*i..2*g] do
                    if l[j-2*i+1] ne 0 and j ne n then m[j]:=m[j]-m[n]; end if;
                end for;
                l:=Eltseq(RowSubmatrix(m,2*i-1,1)*M*Transpose(RowSubmatrix(m,2*i,2*g-2*i+1)));
            end while;
            jr:=2*i-1+Position(l,1);
            zz:=m[2*i]; m[2*i]:=m[jr]; m[jr]:=zz;
        
        for j in [2*i+1..2*g] do
            m[j]:=m[j]+(RowSubmatrix(m,j,1)*M*Transpose(RowSubmatrix(m,2*i-1,1)))[1][1]*m[2*i]-(RowSubmatrix(m,j,1)*M*Transpose(RowSubmatrix(m,2*i,1)))[1][1]*m[2*i-1];
        end for;
    end for;
    P:=ZeroMatrix(IntegerRing(),2*g,2*g);
    for i in [1..g] do
        P[i]:=m[2*i-1];
        P[g+i]:=m[2*i];
    end for;


    P:=Transpose(P);  //Chage of basis matrix
    sj:=Transpose(P)*M*P; //canonical symplectic matrix
    return sj,P;
end function;

//Given a list of matrices L in Sp(2g) attempts to find split the vector space into 2 L-invariant subspaces of dimension g, each consistig of loops with 0 symplectic product.
/*
Busca un subespacio de la homologia de dimension igual al genero que sea invariante bajo el grupo y donde la forma simplectica se anule
Para lograr esto, prueba con las orbitas de vectores en la homologia que tengan componentes 0,1 y -1.
Se limita a vectores con soporte acotado por cota*/
SplitSpace:=function(L)
    g:=NumberOfRows(L[1])div 2;
    Z2g:=RSpace(IntegerRing(),2*g);
    J:=SymplecticMatrix(g);
    tup:=[Vector([0:i in [1..2*g]])];
    LW:=[];
    for i in [1..cota] do
        print "trying with support of size ",i;
        tup2:=[];
        for l in tup do
            for j in [1..2*g] do
                t:=l;
                if t[j] eq 0 then t[j]:=1; Append(~tup2,t);t[j]:=-1; Append(~tup2,t);  end if;
            end for;
        end for;
        tup:=tup2;
        for v in tup do
            l0:=[i*Transpose(Matrix(v)): i in L];    
            l1:=[(v*J*i)[1]:i in l0];
            l2:=[Vector(Transpose(v)):v in l0];
            W:=sub<Z2g|l2>;
            if forall(t){i:i in l1|i eq 0} and Dimension(W) eq g then Append(~LW,W); end if;
        end for;
        for j in [1..#LW] do
            for k in [j+1..#LW] do
                W:=LW[j]+LW[k];
                if Dimension(W) eq 2*g then 
                    m:=Matrix(Basis(LW[j]) cat Basis(LW[k])); 
                    if Abs(Determinant(m)) eq 1 then return m; 
                    end if;
                end if;
            end for;
        end for;
    end for;
/*
Completa una matriz simplectica de cambio de base en caso de haber encontrado solo un espacio invariante apropiado.
Con este cambio, la representacion simplectica del grupo tendra ceros en el bloque inferior izquierdo.
*/
    if LW ne [] then
        Q2g:=VectorSpace(RationalField(),2*g);
        for W in LW do
            B1:=[Q2g!i:i in Basis(W)];
            m:=Matrix(MyExtendBasis(B1,Q2g));
            if Abs(Determinant(m)) eq 1 then return Matrix(IntegerRing(),m); end if;
        end for; 
    end if;
    return 0;
end function;

BetterBasis:=function(L)
    g:=NumberOfRows(L[1])div 2;
    m:=SplitSpace(L);
    if m eq 0 then return 1; end if;
    J:=SymplecticMatrix(g);
    for i in [1..g] do
        l:=Eltseq(RowSubmatrix(m,i,1)*J*Transpose(RowSubmatrix(m,g+i,g-i+1)));
        while not 1 in l do
            for j in [g+i..2*g] do
                if l[j-g-i+1] lt 0 then m[j]:=-m[j]; end if;
            end for;
            l:=Eltseq(RowSubmatrix(m,i,1)*J*Transpose(RowSubmatrix(m,g+i,g-i+1)));
            n:=Min([i : i in l|i ne 0]);
            n:=Position(l,n)+g+i-1;
            for j in [g+i..2*g] do
                if l[j-g-i+1] ne 0 and j ne n then m[j]:=m[j]-m[n]; end if;
            end for;
            l:=Eltseq(RowSubmatrix(m,i,1)*J*Transpose(RowSubmatrix(m,g+i,g-i+1)));
        end while;
        jr:=g+i-1+Position(l,1);
        zz:=m[g+i]; m[g+i]:=m[jr]; m[jr]:=zz;
        for j in [g+i+1..2*g] do
            m[j]:=m[j]+(RowSubmatrix(m,j,1)*J*Transpose(RowSubmatrix(m,i,1)))[1][1]*m[g+i]-(RowSubmatrix(m,j,1)*J*Transpose(RowSubmatrix(m,g+i,1)))[1][1]*m[i];
        end for;
        for j in [g+1..g+i-1] do
            m[j]:=m[j]+(RowSubmatrix(m,j,1)*J*Transpose(RowSubmatrix(m,i,1)))[1][1]*m[g+i]-(RowSubmatrix(m,j,1)*J*Transpose(RowSubmatrix(m,g+i,1)))[1][1]*m[i];
        end for;
    end for;
    for i in [1..g] do
        for j in [g+i+1..2*g] do
            m[j]:=m[j]+(RowSubmatrix(m,j,1)*J*Transpose(RowSubmatrix(m,i,1)))[1][1]*m[g+i]-(RowSubmatrix(m,j,1)*J*Transpose(RowSubmatrix(m,g+i,1)))[1][1]*m[i];
        end for;
    end for;
    return Transpose(m);
end function;
