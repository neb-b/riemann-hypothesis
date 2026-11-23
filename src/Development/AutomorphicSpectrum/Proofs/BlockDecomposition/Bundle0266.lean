module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.Bundle0002
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0229
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0230
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickJIsNilpotent
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SiteNil

theorem thick_J_isNilpotent : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R}
    {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} (T : Thick (nlFun γ p X q κ)), ∀ x ∈ T.J, IsNilpotent x := by
  intro O R _ _ I γ p X q κ T x hx
  by_cases hp : p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have h : x ^ n ∈ T.J ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at h
    exact h
  · obtain ⟨n, hn⟩ : IsNilpotent ((p : ℕ) : T.B) := T.adm.1 hp
    refine ⟨p * n, ?_⟩
    have h1 : x ^ p = (p.factorial : T.B) * T.δ.dpow p x := (T.δ.factorial_mul_dpow_eq_pow hx).symm
    have h2 : (p.factorial : T.B) = (p : T.B) * ((p - 1).factorial : T.B) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp]
    rw [pow_mul, h1, h2, mul_assoc, mul_pow, hn, zero_mul]

end GlobalTheory.CompanionTheory.SiteNil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeFiltrationQuotient
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SiteTrCrit

variable {B : Type} [CommRing B] {J : Ideal B}

theorem sum_eq (δ : DividedPowers J) (b : ℕ →₀ B) :
    (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) =
      Finsupp.linearCombination B (pq B).e b := by
  rw [Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [(eta_std δ).var k, Algebra.smul_def]

theorem repr_sum (δ : DividedPowers J) (b : ℕ →₀ B) :
    (pq B).e.repr (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) = b := by
  rw [sum_eq]
  exact (pq B).e.repr_linearCombination b

theorem crit_sup (δ : DividedPowers J) (r : ℕ) (z : (pq B).P) (c : B) :
    z ∈ fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c} ↔
      ∀ k, (pq B).e.repr z k ∈ fil δ (r - k) ⊔ Ideal.span {c} := by
  have crit := (GlobalTheory.CompanionTheory.PDFil.fil_pdPoly δ (pq B) (eta δ) (eta_std δ)).2.2.2 r
  constructor
  · intro hz k
    obtain ⟨f, hf, g, hg, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    have e : w * algebraMap B (pq B).P c = c • w := by rw [Algebra.smul_def, mul_comm]
    rw [e, map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mem_sup_left ((crit f).1 hf k))
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)))
  · intro h
    rw [← (pq B).e.linearCombination_repr z, Finsupp.linearCombination_apply]
    refine Ideal.sum_mem _ fun k _ => ?_
    obtain ⟨f, hf, g, hg, e⟩ := Submodule.mem_sup.1 (h k)
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    rw [← e]
    beta_reduce
    rw [add_smul]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ((crit _).2 fun j => ?_)) (Ideal.mem_sup_right ?_)
    · rw [map_smul, (pq B).e.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]
      split_ifs with hj
      · rw [← hj]; exact hf
      · exact Ideal.zero_mem _
    · rw [mul_comm w c, mul_smul, Algebra.smul_def c]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.CompanionTheory.SiteTrCrit


open GlobalTheory.CompanionTheory.SiteTrCrit in
theorem GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → ∀ (b : ℕ →₀ B) (r : ℕ), r ≤ s → ∀ c : B, (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ↔ ∀ k, b k ∈ fil δ (r - k)) ∧ (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ⊔ Ideal.span {Ideal.Quotient.mk (fil (eta δ) (max s 1)) (algebraMap B (pq B).P c)} ↔ ∀ k, b k ∈ fil δ (r - k) ⊔ Ideal.span {c}) := by
  intro B _ J δ s δ' hδ' b r hr c
  have hK : fil (eta δ) (max s 1) ≤ fil (eta δ) r :=
    GlobalTheory.Cris.ExpBij.dpFil_anti (eta δ) (le_max_of_le_left hr)
  have hfil : fil δ' r = (fil (eta δ) r).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))) :=
    le_antisymm (FubiniStudyChowHeightFormula₂.Adr.Fil.fil_le_map_fil _ _ (eta δ) _ _ δ' _ hδ' rfl r)
      (FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le (eta δ) δ' _ hδ' r)
  have hsup : (fil (eta δ) r).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))) ⊔
      Ideal.span {Ideal.Quotient.mk (fil (eta δ) (max s 1)) (algebraMap B (pq B).P c)} =
      (fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c}).map
        (Ideal.Quotient.mk (fil (eta δ) (max s 1))) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  rw [hfil, hsup, Ideal.mem_quotient_iff_mem hK, Ideal.mem_quotient_iff_mem (hK.trans le_sup_left),
    crit_sup, (GlobalTheory.CompanionTheory.PDFil.fil_pdPoly δ (pq B) (eta δ) (eta_std δ)).2.2.2, repr_sum]
  exact ⟨Iff.rfl, Iff.rfl⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeTorsionFree
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SiteTr

theorem tr_tf : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (l s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → fil δ s = ⊥ → (∀ (r : ℕ) (x : B), (l : B) * x ∈ fil δ r → x ∈ fil δ r) → fil δ' s = ⊥ ∧ (∀ (r : ℕ) (x : (pq B).P ⧸ fil (eta δ) (max s 1)), (l : (pq B).P ⧸ fil (eta δ) (max s 1)) * x ∈ fil δ' r → x ∈ fil δ' r) ∧ IsNilpotent (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1)))) := by
  intro B _ J δ l s δ' hδ' hs ht
  obtain ⟨-, hanti, h0, crit⟩ := _root_.GlobalTheory.CompanionTheory.PDFil.fil_pdPoly δ (pq B) (eta δ) (eta_std δ)
  have hanti' : ∀ a c, a ≤ c → fil (eta δ) c ≤ fil (eta δ) a := fun a c h =>
    GlobalTheory.Cris.ExpBij.dpFil_anti (eta δ) h
  have hmap : ∀ r, fil δ' r = (fil (eta δ) r).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))) := fun r =>
    le_antisymm (FubiniStudyChowHeightFormula₂.Adr.Fil.fil_le_map_fil _ _ (eta δ) _ _ δ' _ hδ' rfl r)
      (FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le (eta δ) δ' _ hδ' r)
  have htop : fil δ' (max s 1) = ⊥ := by rw [hmap, Ideal.map_quotient_self]
  refine ⟨?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos s with rfl | hpos
    · have h10 : (1 : B) = 0 := by
        have : (1 : B) ∈ fil δ 0 := by rw [h0]; trivial
        rwa [hs, Ideal.mem_bot] at this
      haveI : Subsingleton B := subsingleton_of_zero_eq_one h10.symm
      haveI : Subsingleton (pq B).P := Module.subsingleton B (pq B).P
      haveI : Subsingleton ((pq B).P ⧸ fil (eta δ) (max 0 1)) :=
        Ideal.Quotient.mk_surjective.subsingleton
      exact eq_bot_iff.2 fun x _ => (Ideal.mem_bot).2 (Subsingleton.elim x 0)
    · have e : fil (eta δ) s = fil (eta δ) (max s 1) := by rw [max_eq_left hpos]
      rw [hmap, e, Ideal.map_quotient_self]
  · intro r x hx
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    have key : ∀ y : (pq B).P, Ideal.Quotient.mk (fil (eta δ) (max s 1)) y ∈ fil δ' r ↔
        y ∈ fil (eta δ) (min r (max s 1)) := by
      intro y
      rw [hmap, Ideal.mem_quotient_iff_mem_sup]
      rcases le_total r (max s 1) with h | h
      · rw [min_eq_left h, sup_eq_left.2 (hanti' _ _ h)]
      · rw [min_eq_right h, sup_eq_right.2 (hanti' _ _ h)]
    have hz : (l : (pq B).P) * z ∈ fil (eta δ) (min r (max s 1)) :=
      (key _).1 (by simpa only [map_mul, map_natCast] using hx)
    refine (key z).2 ((crit _ z).2 fun k => ht _ _ ?_)
    have h1 := (crit _ _).1 hz k
    have e : (pq B).e.repr ((l : (pq B).P) * z) k = (l : B) * (pq B).e.repr z k := by
      rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
    rwa [e] at h1
  · have hp : ∀ n, (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1)))) ^ n ≤ fil δ' n := by
      intro n
      induction n with
      | zero =>
        intro a _
        exact GlobalTheory.Cris.ExpBij.mem_dpFil_zero δ' a
      | succ n ih =>
        rw [pow_succ]
        exact Ideal.mul_le.2 fun a ha b hb =>
          GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ' (ih ha) (GlobalTheory.Cris.ExpBij.mem_dpFil_one δ' hb)
    exact ⟨max s 1, le_bot_iff.1 ((hp _).trans htop.le)⟩

end GlobalTheory.CompanionTheory.SiteTr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE

abbrev PO (R : Type) [CommRing R] (N : ℕ) : Over (Spec (CommRingCat.of R)) :=
  Over.mk (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N)

abbrev thickι (R : Type) [CommRing R] (I : Ideal R) (N e : ℕ) :
    (thickObj R I e (PO R N)).left ⟶ PSpace R N :=
  pullback.fst (PO R N).hom (thick R I e)

variable {R : Type} [CommRing R] {N : ℕ}

def HomogIdeal {B : Type} [CommRing B] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) B)) : Prop :=
  ∀ (d : ℕ) (f : MvPolynomial (Fin n) B), f ∈ P → homogeneousComponent d f ∈ P

def KillsForm {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R)
    (hf : f.IsHomogeneous n) : Prop :=
  ∀ k, (φ.app (GlobalTheory.ProjSpace.chart R N k)).hom
    (GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n f hf) = 0

def vanIdeal {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) : Ideal (MvPolynomial (Fin (N + 1)) R) :=
  Ideal.span {f | ∃ n, ∃ hf : f.IsHomogeneous n, KillsForm φ n f hf}


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem vanIdeal_homog {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) : HomogIdeal (vanIdeal φ) := by
  intro d f hf
  have hI : (vanIdeal φ).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) R) := by
    apply Ideal.homogeneous_span
    rintro x ⟨n, hx, -⟩
    exact ⟨n, (mem_homogeneousSubmodule n x).mpr hx⟩
  exact homogeneousComponent_mem_of_mem hI hf d

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VeryAmpleTensorPowerSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem mem_basicOpen_prod {X : Scheme.{0}} {U : X.Opens} {ι : Type} (s : Finset ι) (g : ι → Γ(X, U)) {y : X}
    (hy : y ∈ U) : y ∈ X.basicOpen (∏ l ∈ s, g l) ↔ ∀ l ∈ s, y ∈ X.basicOpen (g l) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Scheme.basicOpen_one, Finset.notMem_empty, false_imp_iff, implies_true, iff_true]
    exact hy
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Scheme.basicOpen_mul, Finset.forall_mem_insert, ← ih]
    rfl

theorem mem_nonzeroLocus_secMono {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D)
    (a : τ → LB.Sec (pw L d)) (w : Fin k → τ) (hk : 1 ≤ k) (y : X) :
    y ∈ nonzeroLocus (secMono h a w) ↔ ∀ l, y ∈ nonzeroLocus (a (w l)) := by
  constructor
  · intro hy l
    obtain ⟨c, hc⟩ := exists_chart_of_mem_nonzeroLocus hy
    have h1 := (mem_nonzeroLocus_iff_basicOpen (secMono h a w) hc).1 hy
    exact (mem_nonzeroLocus_iff_basicOpen (a (w l)) hc).2
      ((mem_basicOpen_prod Finset.univ (fun l => chartFn (a (w l)) c) hc).1 h1 l (Finset.mem_univ l))
  · intro hy
    obtain ⟨c, hc⟩ := exists_chart_of_mem_nonzeroLocus (hy ⟨0, hk⟩)
    refine (mem_nonzeroLocus_iff_basicOpen (secMono h a w) hc).2 ?_
    exact (mem_basicOpen_prod Finset.univ (fun l => chartFn (a (w l)) c) hc).2 fun l _ =>
      (mem_nonzeroLocus_iff_basicOpen (a (w l)) hc).1 (hy l)

theorem prod_update_eq_mul {B τ : Type} [CommMonoid B] {k : ℕ} (φ : τ → B) (w : Fin k → τ) (l : Fin k) (c : τ)
    (ρ : B) (h : φ c = ρ * φ (w l)) :
    ∏ l', φ (Function.update w l c l') = ρ * ∏ l', φ (w l') := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l),
    ← Finset.mul_prod_erase Finset.univ (fun l' => φ (w l')) (Finset.mem_univ l), Function.update_self, h, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun l' hl' => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl')]

theorem secRatio_secMono_update {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D)
    (a : τ → LB.Sec (pw L d)) (w : Fin k → τ) (l : Fin k) (c : τ)
    (hl : nonzeroLocus (secMono h a w) ≤ nonzeroLocus (a (w l))) :
    secRatio (secMono h a w) (secMono h a (Function.update w l c)) = resG X hl (secRatio (a (w l)) (a c)) := by
  refine (eq_secRatio _ _ fun κ => ?_).symm
  have key := secRatio_on (a (w l)) (a c) κ
    (W := nonzeroLocus (secMono h a w) ⊓ (pw L D).U κ) (inf_le_left.trans hl) inf_le_right
  have := prod_update_eq_mul (fun t => resG X (inf_le_right : nonzeroLocus (secMono h a w) ⊓ (pw L D).U κ ≤ L.U κ)
    (chartFn (a t) κ)) w l c _ key
  change resG X _ (∏ l', chartFn (a (Function.update w l c l')) κ) = _ * resG X _ (∏ l', chartFn (a (w l')) κ)
  rw [map_prod, map_prod, resG_resG]
  exact this

theorem mem_of_basicOpen {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) (F : Γ(X, U))
    (hV : V = X.basicOpen F) (hle : V ≤ U) (S : Subring Γ(X, V)) (h1 : ∀ x, resG X hle x ∈ S)
    (g : Γ(X, V)) (hg : g ∈ S) (hgF : g * resG X hle F = 1) (z : Γ(X, V)) : z ∈ S := by
  subst hV
  have := hU.isLocalization_basicOpen F
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers F) z
  have hx' : z * resG X hle F ^ n = resG X hle x := by
    have e : ∀ t, algebraMap Γ(X, U) Γ(X, X.basicOpen F) t = resG X hle t := fun _ => rfl
    simpa only [e, map_pow] using hx
  have : z = resG X hle x * g ^ n := by
    rw [← hx', mul_assoc, ← mul_pow, mul_comm (resG X hle F), hgF, one_pow, mul_one]
  rw [this]
  exact S.mul_mem (h1 x) (S.pow_mem hg n)

theorem veryAmpleBy_secMono : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (d D : ℤ) (k : ℕ) (h : d * k = D) (p : ℕ) (a : Fin (p + 1) → LB.Sec (pw L d)), L.IsLB → 1 ≤ k → VeryAmpleBy f (pw L d) a → ∀ (m : ℕ) (e : Fin (m + 1) ≃ (Fin k → Fin (p + 1))), VeryAmpleBy f (pw L D) (fun j => secMono h a (e j)) := by
  intro R _ X f L d D k h p a hL hk hva m e
  obtain ⟨hcov, hch⟩ := hva
  refine ⟨?_, fun j => ?_⟩
  · refine top_unique ?_
    rw [← hcov]
    refine iSup_le fun i => ?_
    rw [← nonzeroLocus_secMono_const h a i hk]
    refine le_trans ?_ (le_iSup _ (e.symm fun _ => i))
    simp only [Equiv.apply_symm_apply, le_refl]
  · beta_reduce
    let w : Fin k → Fin (p + 1) := e j
    let l₀ : Fin k := ⟨0, hk⟩
    obtain ⟨hU, r, hr, hsurj⟩ := hch (w l₀)
    obtain rfl : r = fun t => secRatio (a (w l₀)) (a t) := funext fun t => eq_secRatio _ _ (hr t)
    have hN : ∀ l, nonzeroLocus (secMono h a w) ≤ nonzeroLocus (a (w l)) := fun l y hy =>
      (mem_nonzeroLocus_secMono h a w hk y).1 hy l
    have hV : nonzeroLocus (secMono h a w) = X.basicOpen (∏ l, secRatio (a (w l₀)) (a (w l))) := by
      ext y
      constructor
      · intro hy
        refine (mem_basicOpen_prod Finset.univ _ (hN l₀ hy)).2 fun l _ => ?_
        rw [basicOpen_secRatio]
        exact ⟨hN l₀ hy, hN l hy⟩
      · intro hy
        have hy₀ := X.basicOpen_le _ hy
        refine (mem_nonzeroLocus_secMono h a w hk y).2 fun l => ?_
        have := (mem_basicOpen_prod Finset.univ _ hy₀).1 hy l (Finset.mem_univ l)
        rw [basicOpen_secRatio] at this
        exact this.2
    refine ⟨hV ▸ hU.basicOpen _, fun t => secRatio (secMono h a w) (secMono h a (e t)),
      fun t κ => secRatio_spec _ _ κ, fun z => ?_⟩
    let S := (MvPolynomial.eval₂Hom (cst f (nonzeroLocus (secMono h a w)))
      fun t => secRatio (secMono h a w) (secMono h a (e t))).range
    have hρ : ∀ v, secRatio (secMono h a w) (secMono h a v) ∈ S := fun v =>
      ⟨MvPolynomial.X (e.symm v), by simp⟩
    have hC : ∀ c : R, cst f (nonzeroLocus (secMono h a w)) c ∈ S := fun c =>
      ⟨MvPolynomial.C c, by simp⟩
    have h1 : ∀ x, resG X (hN l₀) x ∈ S := fun x => by
      obtain ⟨P, rfl⟩ := hsurj x
      induction P using MvPolynomial.induction_on with
      | C c =>
        rw [MvPolynomial.eval₂Hom_C]
        exact (rs_cst f (hN l₀) c).symm ▸ hC c
      | add P Q hP hQ =>
        rw [map_add (f := _), map_add (f := _)]
        exact S.add_mem hP hQ
      | mul_X P t hP =>
        rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']
        refine S.mul_mem hP ?_
        rw [← secRatio_secMono_update h a w l₀ t (hN l₀)]
        exact hρ _
    obtain ⟨P, hP⟩ : z ∈ S := mem_of_basicOpen hU _ hV (hN l₀) S h1
      (∏ l, secRatio (secMono h a w) (secMono h a (Function.update w l (w l₀))))
      (S.prod_mem fun l _ => hρ _) (by
        rw [map_prod, ← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun l _ => ?_
        rw [secRatio_secMono_update h a w l (w l₀) (hN l), mul_comm,
          secRatio_mul_secRatio _ _ _ (hN l₀) (hN l), secRatio_self, map_one]) z
    exact ⟨P, hP⟩

end GlobalTheory.CompanionTheory.FormalAlg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VeryAmpleUnionSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

namespace GlobalTheory.CompanionTheory.VeryAmpleUnion

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def ChartBy (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (a : LB.Sec H) {m : ℕ}
    (s : Fin (m + 1) → LB.Sec H) : Prop :=
  IsAffineOpen (nonzeroLocus a) ∧
    ∃ r : Fin (m + 1) → Γ(X, nonzeroLocus a),
      (∀ j k, rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) ((s j).f k) =
        rs X (inf_le_left : nonzeroLocus a ⊓ H.U k ≤ nonzeroLocus a) (r j) *
          rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) (a.f k)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (cst f (nonzeroLocus a)) r)

theorem ChartBy.of_sub {f : X ⟶ Spec (CommRingCat.of R)} {H : LB X} {a : LB.Sec H} {m n : ℕ}
    {w : Fin (n + 1) → LB.Sec H} {z : Fin (m + 1) → LB.Sec H} (ι : Fin (n + 1) → Fin (m + 1))
    (hι : ∀ l, z (ι l) = w l) (h : ChartBy f H a w) : ChartBy f H a z := by
  obtain ⟨ha, r, hr, hs⟩ := h
  refine ⟨ha, fun j => secRatio a (z j), fun j k => secRatio_spec a (z j) k, fun g => ?_⟩
  obtain ⟨p, rfl⟩ := hs g
  refine ⟨MvPolynomial.rename ι p, ?_⟩
  have hrr : (fun j => secRatio a (z j)) ∘ ι = r := by
    funext l
    refine (eq_secRatio a (z (ι l)) ?_).symm
    intro k
    rw [hι l]
    exact hr l k
  simp only [MvPolynomial.coe_eval₂Hom]
  rw [MvPolynomial.eval₂_rename, hrr]

theorem veryAmpleBy_union : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X), H.IsLB → ∀ (m₁ m₂ m : ℕ) (x : Fin (m₁ + 1) → LB.Sec H) (y : Fin (m₂ + 1) → LB.Sec H) (e : Fin (m + 1) ≃ Fin (m₁ + 1) ⊕ Fin (m₂ + 1)), VeryAmpleBy f H x → VeryAmpleBy f H y → VeryAmpleBy f H (fun j => Sum.elim x y (e j)) := by
  intro R _ X f H _ m₁ m₂ m x y e hx hy
  have key : ∀ (z : Fin (m + 1) → LB.Sec H), (∀ j, z j = Sum.elim x y (e j)) →
      (⨆ j, nonzeroLocus (z j) = ⊤) ∧ ∀ j, ChartBy f H (z j) z := by
    intro z hz
    have hl : ∀ i, z (e.symm (Sum.inl i)) = x i := fun i => by simp [hz]
    have hr : ∀ i, z (e.symm (Sum.inr i)) = y i := fun i => by simp [hz]
    refine ⟨eq_top_iff.2 ?_, fun j => ?_⟩
    · rw [← hx.1]
      exact iSup_le fun i => le_iSup_of_le (e.symm (Sum.inl i)) (by rw [hl])
    · rcases he : e j with i | i
      · have hj : z j = x i := by rw [hz, he]; rfl
        rw [hj]
        exact ChartBy.of_sub (fun l => e.symm (Sum.inl l)) hl (hx.2 i)
      · have hj : z j = y i := by rw [hz, he]; rfl
        rw [hj]
        exact ChartBy.of_sub (fun l => e.symm (Sum.inr l)) hr (hy.2 i)
  exact key _ fun _ => rfl

end GlobalTheory.CompanionTheory.VeryAmpleUnion
end

