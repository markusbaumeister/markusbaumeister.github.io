# This computation follows the subgroup presentation algorithm
# from the Handbook of Computational Group Theory

# For details, consult Theorem 9.5.7 of my PhD-thesis.

# Given a homomorphism from a free group into a factor group,
# compute the Schreier transversal of its kernel
SchreierTransversal := function( hom )
    local trans, todo, imageList, gens, word, g, free;

    free := Source(hom);
    trans := [];
    todo := [ One(free) ];
    gens := GeneratorsOfGroup(free);
    imageList := [];
    while not IsEmpty(todo) do;
        word := Remove(todo, 1);
        # Check if this element already was found
        if not Image(hom, word) in imageList then
            Add(trans, word);
            Add(imageList, Image(hom, word));
            for g in gens do
                Add(todo, word*g);
            od;
        fi;
    od;

    return trans;
end;

# Given an element in the free group, the homomorphism into
# a factor group and the transversal of the kernel, return
# the representative of the element in the transversal
SchreierRep := function( el, hom, transversal )
    local test;

    for test in transversal do
        if Image(hom, test) = Image(hom, el) then
            return test;
        fi;
    od;

    Error("No representative found.");
end;

# Given a homomorphism, a transversal of its kernel and two
# elements t,x, compute their Schreier generator
SchreierGenerator := function( hom, transversal, t, x )
    return t * x * SchreierRep( t*x, hom, transversal )^(-1);
end;

# The primes are chosen by uncommenting one of the following three lines
# p := 2; pk := p^3;
# p := 3; pk := p^2;
# p := 5; pk := p^1;


F := FreeGroup( "a", "b", "c" );
generalRel := [ F.a^2, F.b^2, F.c^2, (F.a*F.c)^2, (F.a*F.b)^3 ];
Hgen := F/generalRel;
# Map from F to Hgen
homGen := GroupHomomorphismByImages( F, Hgen, 
                [F.a,F.b,F.c], [Hgen.1,Hgen.2,Hgen.3]);

Ngen := NormalClosure( Hgen, 
    Group([ (Hgen.2*Hgen.3)^pk, (Hgen.2*Hgen.1*Hgen.3)^pk ]) );
# Map from Hgen to N_{p^k}
homNgen := NaturalHomomorphismByNormalSubgroup(Hgen, Ngen);
# Map from F to N_{p^k}
homNinfree := CompositionMapping2( homNgen, homGen );
Hpk := Image(homNgen);

transversal := SchreierTransversal( homNinfree );
schreierGens := [];
for t in transversal do
    for x in [F.a,F.b,F.c] do
        Add(schreierGens, 
            [t,x,SchreierGenerator(homNinfree, transversal, t,x)]);
    od;
od;

simpleRelations := [];
for rel in generalRel do
    for t in transversal do
        Add( simpleRelations, t*rel*t^(-1) );
    od;
od;

# Rewrite the simple relations in the Schreier-generators
subgroup := Group( List(schreierGens, i->i[3]) );
rewriteHom := EpimorphismFromFreeGroup( subgroup );
G := Source(rewriteHom);

newRels := [];
for i in [1..Length(schreierGens)] do
    if schreierGens[i][3] = Identity(F) then
        Add(newRels, G.(i));
    fi;
od;
for rel in simpleRelations do
    Add(newRels, PreImagesRepresentative(rewriteHom, rel));
od;


pres := PresentationFpGroup(G/newRels);
TzGoGo(pres);


remainingIndices := [];
for gen in GeneratorsOfPresentation(pres) do
    # This is a hack to obtain the number of the generator
    str := ShallowCopy( String(gen) );
    Remove(str,1);
    pos := Int(str);
    Add( remainingIndices, pos );
od;


minSubgroup := Group( List( remainingIndices, 
    i -> Image(homGen, schreierGens[i][3])  ) ); # subgroup of Hgen
minRewriteHom := EpimorphismFromFreeGroup( minSubgroup );
a := Hgen.1;
b := Hgen.2;
c := Hgen.3;


bcList := List( transversal, 
    t -> Image(homGen, t)^(-1) * (b*c)^pk * Image(homGen, t) );
bacList := List( transversal, 
    t -> Image(homGen, t)^(-1) * (b*a*c)^pk * Image(homGen, t) );
paramRels := Set(Concatenation(bcList, bacList));

trueRels := List(paramRels, 
    rel -> PreImagesRepresentative(minRewriteHom, rel));
minRels := [];
for t in trueRels do
    found := false;
    for m in minRels do
        if t = m or t = m^(-1) then
            found := true;
        fi;
    od;
    if not found then
        Add(minRels, t);
    fi;
od;

coreQuotient := Source(minRewriteHom)/List(minRels, r -> r^p);
AbelianInvariants(coreQuotient);

