=encoding utf8

=head1 NAME

CInet::Adhesive - Blackbox selfadhesivity testing

=head1 SYNOPSIS

    my $bool = is_selfadhesive($A, $oracle);

=cut

# ABSTRACT: Blackbox selfadhesivity testing
package CInet::Adhesive;

use utf8;
use Modern::Perl 2018;
use Export::Attrs;

use CInet::Base;
use Array::Set qw(set_diff);
use List::Util qw(all any);
use Algorithm::Combinatorics qw(subsets);

=head1 DESCRIPTION

This module implements a structural selfadhesivity test using an oracle
for the base family of CI relations.

=head2 EXPORTS

Two functions are exported by default:

    my $bool = is_selfadhesive_at($A, $oracle, $I)
    my $bool = is_selfadhesive($A, $oracle, $orders);

=cut

=head3 is_selfadhesive_at

    my $bool = is_selfadhesive_at($A, $oracle, $I)

Tests if C<$A> is selfadhesive at the set C<$I> with respect to the family
defined by C<$oracle>. That coderef must accept a CI structure on any
ground set and decide if it belongs to the family or not.

=cut

sub is_selfadhesive_at :Export(:DEFAULT) {
    my ($x, $realiz, $I) = @_;
    my $Ncube = Cube($x);
    my $N = $Ncube->set;
    my $K = set_diff($N, $I);

    # $realiz algorithms tend to cache parts of their setup based on the
    # ->cube of their argument. By permuting $I to the initial segment of
    # $N avoids the creation of lots of isomorphic cubes and the caches
    # associated to them. This assumes that $realiz is invariant under
    # isomorphy!
    my $p = do {
        my $p;
        my @elts = @$N; # copy of @$N in its natural order
        $p->[$_] = shift(@elts)
            for $Ncube->_index(@$I, @$K); # (@$I, @$K) in that order!
        $p
    };
    $I = [ $N->@[0 .. $I->$#*] ];
    $K = set_diff($N, $I);
    $x = $x->permute($p);

    # Make a copy of N but prefix all axes not in I with a string to make
    # them different from their N preimages. Then join the two cubes.
    my $prefix = 0+ $I->@*;
    my %NtoM = (
        map({ $_ =>     "$_"     } @$I),
        map({ $_ => "$prefix^$_" } @$K),
    );
    my $M = [ map $NtoM{$_}, @$N ];
    my $L = set_diff($M, $I);

    my $NMcube = Cube [@$K, @$L, @$I];

    # Now define the selfadhesivity certificate as a partial relation.
    my $S = CInet::Relation->new($NMcube);
    # 1. $S restricted to $N must be $x,
    # 2. $S restricted to $M must be $x.
    for my $ijK ($Ncube->squares) {
        # Translate N-symbol to M-symbol
        my $MijK = [ map { [ map $NtoM{$_}, @$_ ] } @$ijK ];
        $S->cival($ijK) = $S->cival($MijK) = $x->cival($ijK);
    }
    # 3. The independence (K,L|I) must hold. To encode the global CI
    # statement as a conjunction of local ones, we assume only the
    # semigraphoid axioms!
    for my $k (@$K) {
        for my $l (@$L) {
            for my $P (subsets(set_diff($NMcube->set, [$k, $l, @$I]))) {
                $S->cival([ [$k, $l], [@$I, @$P] ]) = 0;
            }
        }
    }

    # Check consistency.
    $realiz->($S)
}

=head3 is_selfadhesive

    my $bool = is_selfadhesive($A, $oracle, $orders)

This function calls L<is_selfadhesive_at|/"is_selfadhesive_at"> with
all subsets C<$I> that have cardinality in the arrayref C<$orders>.
If C<$orders> is not given, it defaults to all possible orders between
0 and the dimension of the cube of C<$A>.

=cut


sub is_selfadhesive :Export(:DEFAULT) {
    my ($x, $realiz, $orders) = @_;
    my $cube = Cube($x);
    $orders //= [ 0 .. $cube->dim ];
    return all { is_selfadhesive_at($x, $realiz, $_)  }
        grep { my $k = @$_; any { $_ == $k } @$orders }
        map  { $_->[1] } $cube->vertices
}

=head1 AUTHOR

Tobias Boege <tobs@taboege.de>

=head1 COPYRIGHT AND LICENSE

This software is copyright (C) 2020 by Tobias Boege.

This is free software; you can redistribute it and/or
modify it under the terms of the Artistic License 2.0.

=cut

":wq"
