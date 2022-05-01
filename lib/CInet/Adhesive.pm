# ABSTRACT: Blackbox selfadhesivity testing
package CInet::Adhesive;

use utf8;
use Modern::Perl 2018;
use Export::Attrs;

use CInet::Base;
use Array::Set qw(set_diff)
use List::Util qw(all);
use Algorithm::Combinatorics qw(subsets);

sub is_selfadhesive_at {
    my ($x, $realiz, $I) = @_;
    my $Ncube = Cube($x);
    my $N = $Ncube->set;
    my $K = set_diff($N, $I);
    # Make a copy of N but prefix all axes not in I with a string to make
    # them different from their N preimages. Then join the two cubes.
    my $prefix = join '', sort @$I;
    my %NtoM = (
        map({ $_ =>      $_      } @$I),
        map({ $_ => "$prefix^$_" } @$K),
    );
    my $M = map $NtoM{$_}, @$N;
    my $L = set_diff($M, $I);

    my $NMcube = Cube [@$K, @$L, @$I];

    # Now define the selfadhesivity certificate as a partial relation.
    my $S = CInet::Relation->new($NMcube);
    # 1. $S restricted to $N must be $x,
    # 2. $S restricted to $M must be $x.
    for my $ijK ($Ncube->squares) {
        # Translate N-symbol to M-symbol
        my $MijK = [ map { [ map $NtoM{$_}, @$_ ] } @ijK ];
        $S->[$NMcube->pack($ijK)] = $S->[$NMcube->pack($MijK)] =
            $x->[$Ncube->pack($ijK)];
    }
    # 3. The independence (K,L|I) must hold. To encode the global CI
    # statement as a conjunction of local ones, we assume only the
    # semigraphoid axioms!
    for my $k (@$K) {
        for my $l (@$L) {
            for my $P (subsets(set_diff($NMcube->set, [$k, $l, @$I]))) {
                $S->[$NMcube->pack([ [$k, $l], [@$I, @$P] ])] = 0;
            }
        }
    }

    # Check consistency.
    $realiz->($S)
}

sub is_selfadhesive {
    my ($x, $realiz) = @_;
    return all { selfadhesive_at $x, $realiz, $_ }
        map { $_->[1] } Cube($x)->vertices
}

":wq"
