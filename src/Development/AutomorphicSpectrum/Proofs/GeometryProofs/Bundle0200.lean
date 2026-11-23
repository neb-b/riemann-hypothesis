module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0170
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0199
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedDivisibleGroupExists
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0198
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionThree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0135
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedDescendsToFinitelyGenerate
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem geometricallyConnected_descends_to_fg :
    ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (G : Over (Sp k))
      [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom →
      GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k V))) →
      ∃ R : Subalgebra k V, R.FG ∧
        GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k R))) := by
  intro k V _ _ _ _ G _ _ hs hp hV
  classical
  set U : Set (PrimeSpectrum k) := {x | GeometricallyConnected
      (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} with hUdef
  have hU : IsOpen U := _root_.GlobalTheory.CompanionTheory.Ar.Approx.isOpen_geometricallyConnected_fibres k G hs hp
  have hVU : ∀ x ∈ Set.range (PrimeSpectrum.comap (algebraMap k V)), x ∈ U :=
    (_root_.GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField k V G.left G.hom).1 hV
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hU.isClosed_compl
  have htop : Ideal.map (algebraMap k V) I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hx := hVU (PrimeSpectrum.comap (algebraMap k V) ⟨M, hM.isPrime⟩) ⟨_, rfl⟩
    have hx' : PrimeSpectrum.comap (algebraMap k V) ⟨M, hM.isPrime⟩ ∈ Uᶜ := by
      rw [hI, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal]
      exact Ideal.map_le_iff_le_comap.1 hle
    exact hx' hx
  have h1 : (1 : V) ∈ Submodule.span V (algebraMap k V '' (I : Set k)) := by
    have h := (Ideal.eq_top_iff_one _).1 htop
    exact h
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 h1
  choose f hfI hfg using fun i => (g i).2
  let s : Finset V := Finset.univ.image c
  have hc : ∀ i, c i ∈ Algebra.adjoin k (s : Set V) := fun i =>
    Algebra.subset_adjoin (by simp [s])
  refine ⟨Algebra.adjoin k (s : Set V), Subalgebra.fg_adjoin_finset s, ?_⟩
  apply (_root_.GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField k (Algebra.adjoin k (s : Set V)) G.left G.hom).2
  rintro x ⟨y, rfl⟩
  by_contra hx
  have hx' : PrimeSpectrum.comap (algebraMap k (Algebra.adjoin k (s : Set V))) y ∈ Uᶜ := hx
  rw [hI, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal] at hx'
  have hmem : (∑ i, (⟨c i, hc i⟩ : Algebra.adjoin k (s : Set V)) *
      algebraMap k (Algebra.adjoin k (s : Set V)) (f i)) ∈ y.asIdeal :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hx' (hfI i))
  have hone : (∑ i, (⟨c i, hc i⟩ : Algebra.adjoin k (s : Set V)) *
      algebraMap k (Algebra.adjoin k (s : Set V)) (f i)) = 1 := by
    apply Subtype.ext
    have key : (Algebra.adjoin k (s : Set V)).val (∑ i, (⟨c i, hc i⟩ : Algebra.adjoin k (s : Set V)) *
        algebraMap k (Algebra.adjoin k (s : Set V)) (f i)) = ∑ i, c i • (g i : V) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, AlgHom.commutes, Subalgebra.coe_val, hfg, smul_eq_mul]
    exact key.trans (hsum.trans (by simp))
  exact y.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hone ▸ hmem))

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointHTOfFarguesHodgeTate
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.Fargues

theorem lie_free_finite (S : Scheme.{0}) (G : Over S) [GrpObj G] (hG : Smooth G.hom) (R : Type) [CommRing R]
    [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E]
    (M : LieModel G x E) : Module.Free R E ∧ Module.Finite R E := by
  obtain ⟨n, ⟨b⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieFreeSmooth.lieModel_free_of_smooth S G hG R x E M
  exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

def ordTower (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1)
    (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G]
    [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La]
    [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L]
    (M : LieModel G y L) : OrdTower p O La L :=
  haveI : IsLocalRing O := (_root_.GlobalTheory.CompanionTheory.Ar.HT.padicComplete_integers_structure p C v O hv hp hO).2.1.toIsLocalRing
  have h3 := _root_.GlobalTheory.CompanionTheory.Ar.HT.tw_hopf_main p C v O hv hp hO S G hG y La X
  have h4 := _root_.GlobalTheory.CompanionTheory.Ar.HT.btOrder_restriction p C v O hv hp hO S G hG y La X
  have h5 := _root_.GlobalTheory.CompanionTheory.Ar.HT.TwDer.der_main p C v O hv hp hO S G hG y La X L M
  have h6 := (_root_.GlobalTheory.CompanionTheory.Ar.HT.tw_funct p C v O hv hp hO S G hG y La X L M).1
  { A := fun n => (X.Γ n).btOrder ⊤
    hopf := by
      obtain ⟨U, H, -, -, -, h, -⟩ := h3
      exact h
    res_iff := fun n => (h4 n).1
    ker_res := fun n => (h4 n).2
    der := X.IsDer M
    der_ex := fun n => (h5 n).1
    der_unique := fun n => (h5 n).2.1
    der_onto := fun n => (h5 n).2.2.1
    der_add := fun n f g w w' hf hg => ((h5 n).2.2.2.1 f g w w' hf hg).1
    der_mul := fun n f g w w' hf hg => ((h5 n).2.2.2.1 f g w w' hf hg).2
    der_const := fun n => (h5 n).2.2.2.2.1
    der_zero := fun n => (h5 n).2.2.2.2.2
    der_res := h6 }

theorem pointHT (hF : FarguesHodgeTate) : PointHT := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO E _ _ c hc S _ G _ _ hG y La _ _ EF N u hu X L _ _ M act ρL hmon hact hind
    hrank ζ hζ hζp hpair κ hκ
  haveI : Module.Free ℤ La := hu.free
  haveI : Module.Finite ℤ La := hu.finite
  haveI : IsLocalRing O := (_root_.GlobalTheory.CompanionTheory.Ar.HT.padicComplete_integers_structure p C v O hv hp hO).2.1.toIsLocalRing
  obtain ⟨hLf, hLfin⟩ := lie_free_finite S G hG.smooth O y L M
  let T := ordTower p C v O hv hp hO S G hG y La X L M
  have hacts : ∀ a : 𝓞 E, T.Acts (DistribSMul.toAddMonoidHom La a) (ρL a) := by
    intro a n f g hfg
    haveI := hmon a
    exact (_root_.GlobalTheory.CompanionTheory.Ar.HT.tw_funct p C v O hv hp hO S G hG y La X L M).2 (act a) _ (ρL a) (hind a) (hact a) n f g hfg
  have hpe : T.PairingExtends EF ζ := fun n =>
    _root_.GlobalTheory.CompanionTheory.Ar.HT.pairingRegular_mem_prodSpan p C v O hv hp hO S G hG y La X EF ζ (fun n => (hζ n).pow_eq_one) hpair n
  exact _root_.GlobalTheory.CompanionTheory.Ar.HT.TowerPoint.exists_HTPoint hF p C v O hv hp hO E c hc La EF N u hu L T ρL ζ κ hacts hrank hζ hζp hpe hκ

end GlobalTheory.CompanionTheory.Ar.HT.Fargues
end
end

