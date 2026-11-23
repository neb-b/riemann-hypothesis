module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0157
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0170
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0165
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0166
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0168
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapsSurjectiveWithKernels
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem dxi_zero {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) : A.dxi n 0 = 1 := by
  have h : A.dxi0 0 = 1 := Subtype.ext (by simp [PAlg.dxi0, dpw])
  rw [PAlg.dxi, h, map_one]

theorem exists_toAcr_sub_mem {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (z : A.Acr n) :
    ∃ w : A.W, z - A.toAcr n w ∈ A.Fil n 1 := by
  have h0 : z ∈ A.Fil n 0 := by
    rw [((_root_.GlobalTheory.CompanionTheory.FilMul.main A).2.2.2.2.2.2.1 n)]; trivial
  obtain ⟨w, hw⟩ := (_root_.GlobalTheory.CompanionTheory.PerfFil.graded_mod_pow A n 0).1 z h0
  refine ⟨w, ?_⟩
  simpa [dxi_zero] using hw

theorem toAcr_mem_fil_iff {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (w : A.W) :
    A.toAcr n w ∈ A.Fil n 1 ↔ A.th w ∈ Ideal.span {(l : A.U) ^ n} := by
  have h := (_root_.GlobalTheory.CompanionTheory.PerfFil.graded_mod_pow A n 0).2 w
  simpa [dxi_zero] using h

theorem uToQ_surjective {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    Function.Surjective (A.uToQ n) := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨w, hw⟩ := exists_toAcr_sub_mem A n z
  exact ⟨A.th w, (Ideal.Quotient.eq.2 hw).symm⟩

theorem ker_uToQ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    RingHom.ker (A.uToQ n) = Ideal.span {(l : A.U) ^ n} := by
  ext x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  change A.th w ∈ _ ↔ A.th w ∈ _
  rw [RingHom.mem_ker, uToQ_th, Ideal.Quotient.eq_zero_iff_mem, toAcr_mem_fil_iff]

theorem uToPQ_surjective {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    Function.Surjective (A.uToPQ n) := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨w, hw⟩ := exists_toAcr_sub_mem A n z
  have h : z - A.toAcr n w ∈ A.PFil n := Ideal.mem_sup_right hw
  exact ⟨A.th w, (Ideal.Quotient.eq.2 h).symm⟩

theorem ker_uToPQ {l : ℕ} [Fact l.Prime] (A : PAlg l) {n : ℕ} (hn : n ≠ 0) :
    RingHom.ker (A.uToPQ n) = Ideal.span {(l : A.U)} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    change A.th w ∈ _
    have h : A.toAcr n w ∈ A.PFil n := Ideal.Quotient.eq_zero_iff_mem.1 hx
    obtain ⟨u, hu, z, hz, e⟩ := Submodule.mem_sup.1 h
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    obtain ⟨w', hw'⟩ := exists_toAcr_sub_mem A n a
    have h1 : A.toAcr n (w - (l : A.W) * w') ∈ A.Fil n 1 := by
      have e' : A.toAcr n (w - (l : A.W) * w') = (a - A.toAcr n w') * (l : A.Acr n) + z := by
        rw [map_sub, map_mul, map_natCast, ← e]; ring
      rw [e']
      exact add_mem (Ideal.mul_mem_right _ _ hw') hz
    have h2 := (toAcr_mem_fil_iff A n _).1 h1
    have h3 : A.th (w - (l : A.W) * w') ∈ Ideal.span {(l : A.U)} :=
      Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ hn) h2
    have h4 : A.th w = A.th (w - (l : A.W) * w') + (l : A.U) * A.th w' := by
      rw [map_sub, map_mul, map_natCast]; ring
    rw [h4]
    exact add_mem h3 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_natCast,
      ← map_natCast (Ideal.Quotient.mk (A.PFil n))]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))

theorem uToQ_main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (A.uToQ n) ∧
    RingHom.ker (A.uToQ n) = Ideal.span {(l : A.U) ^ n} ∧ Function.Surjective (A.uToPQ n) ∧
    (n ≠ 0 → RingHom.ker (A.uToPQ n) = Ideal.span {(l : A.U)}) :=
  fun A n => ⟨uToQ_surjective A n, ker_uToQ A n, uToPQ_surjective A n, fun hn => ker_uToPQ A hn⟩

end GlobalTheory.CompanionTheory.Untilt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SqCSmul
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

theorem sqC_add {c c' c'' : R'} (hc : c'' = c + c') {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (ha'' : m.LeC c'' a a') (hb'' : m.LeC c'' b b') (T : C') (x : sqM a b (m.G.obj T)) :
    (m.sqC c'' ha'' hb'').τ T x = (m.sqC c ha hb).τ T x + (m.sqC c' ha' hb').τ T x := by
  subst hc
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (c + c') * m.ρ T y) =
    Ideal.Quotient.mk _ (algebraMap R' _ c * m.ρ T y) + Ideal.Quotient.mk _ (algebraMap R' _ c' * m.ρ T y)
  rw [map_add (f := _), add_mul, map_add (f := _)]

theorem sqC_smul {c c' : R'} (r : R) (hc : c' = σ r * c) {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b') (T : C')
    (x : sqM a b (m.G.obj T)) :
    (m.sqC c' ha' hb').τ T x = (m.sqC c ha hb).τ T (r • x) := by
  subst hc
  rw [LinearMap.map_smulₛₗ]
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (σ r * c) * m.ρ T y) =
    σ r • Ideal.Quotient.mk _ (algebraMap R' _ c * m.ρ T y)
  have h : ∀ z : Φ'.A.obj T, Ideal.Quotient.mk (b'.S T) (algebraMap R' _ (σ r) * z) = σ r • Ideal.Quotient.mk (b'.S T) z :=
    fun z => by rw [← Algebra.smul_def]; rfl
  rw [← h, ← mul_assoc, ← map_mul]

section Pts

variable {d : ℕ} (E : Frame (Φ := Φ) d) (E' : Frame (Φ := Φ') d) (e : E.D ⟶ m.G.obj E'.D)

theorem mPt_add {c c' c'' : R'} (hc : c'' = c + c') {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (ha'' : m.LeC c'' a a') (hb'' : m.LeC c'' b b') (j : ℕ) (x : CH.H (Pt.U E ⋙ sq a b) j) :
    (mPt m E E' e c'' ha'' hb'').pull j x = (mPt m E E' e c ha hb).pull j x + (mPt m E E' e c' ha' hb').pull j x := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c'' ha'' hb'').hom f hf
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c ha hb).hom f hf
  have h3 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c' ha' hb').hom f hf
  change (mPt m E E' e c'' ha'' hb'').hom.mapH j _ = (mPt m E E' e c ha hb).hom.mapH j _ + (mPt m E E' e c' ha' hb').hom.mapH j _
  rw [CrystallineSemistableComparison.P.mapH_cls _ j f hf h1, CrystallineSemistableComparison.P.mapH_cls _ j f hf h2, CrystallineSemistableComparison.P.mapH_cls _ j f hf h3,
    ← (CrystallineSemistableComparison.P.cls_surj _ j).2.2.2.1 _ _ h2 h3 (by rw [map_add (f := _), h2, h3, add_zero])]
  exact cls_congr (funext fun s => sqC_add m hc ha hb ha' hb' ha'' hb'' _ _) _ _

theorem mPt_smul {c c' : R'} (r : R) (hc : c' = σ r * c) {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (j : ℕ) (x : CH.H (Pt.U E ⋙ sq a b) j) :
    (mPt m E E' e c' ha' hb').pull j x = (mPt m E E' e c ha hb).pull j (r • x) := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  have h0 : CH.d _ j (r • f) = 0 := by rw [map_smul]; exact (show r • CH.d _ j f = 0 by rw [show CH.d _ j f = 0 from hf, smul_zero])
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c' ha' hb').hom f hf
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c ha hb).hom (r • f) h0
  rw [← (CrystallineSemistableComparison.P.cls_surj _ j).2.2.2.2 r f hf h0]
  change (mPt m E E' e c' ha' hb').hom.mapH j _ = (mPt m E E' e c ha hb).hom.mapH j _
  rw [CrystallineSemistableComparison.P.mapH_cls _ j f hf h1, CrystallineSemistableComparison.P.mapH_cls _ j _ h0 h2]
  exact cls_congr (funext fun s => sqC_smul m r hc ha hb ha' hb' _ _) _ _

theorem pull_U (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (j : ℕ)
    (x : CH.H (sq a b) j) :
    (mPt m E E' e c ha hb).pull j ((CH.Mor.restrict (sq a b) (Pt.U E)).pull j x) =
      (CH.Mor.restrict (sq a' b') (Pt.U E')).pull j ((m.sqC c ha hb).pull j x) := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  rfl

end Pts

section HAdd

variable {R'' : Type} [CommRing R''] [Algebra R R''] {Ψ : PDF R'' C'} (p : SMor Φ Ψ (algebraMap R R''))
  {d : ℕ} (E : Frame (Φ := Φ) d) (E' : Frame (Φ := Ψ) d) (e : E.D ⟶ p.G.obj E'.D)

theorem hadd_Pt {N : Type} [AddCommGroup N] [Module R N] (ν : N →ₗ[R] R'') {a b : IdF Φ.A} {a' b' : IdF Ψ.A}
    (ha : ∀ n, p.LeC (ν n) a a') (hb : ∀ n, p.LeC (ν n) b b') (j : ℕ) :
    ∃ F : N ⊗[R] CH.H (Pt.U E ⋙ sq a b) j →+ CH.H (Pt.U E' ⋙ sq a' b') j,
      ∀ n x, F (n ⊗ₜ x) = (mPt p E E' e (ν n) (ha n) (hb n)).pull j x := by
  let f : N →+ (CH.H (Pt.U E ⋙ sq a b) j →+ CH.H (Pt.U E' ⋙ sq a' b') j) :=
    AddMonoidHom.mk' (fun n => ((mPt p E E' e (ν n) (ha n) (hb n)).pull j).toAddMonoidHom) (fun n n' => AddMonoidHom.ext fun x =>
      mPt_add p E E' e (map_add ν n n') (ha n) (hb n) (ha n') (hb n') (ha _) (hb _) j x)
  refine ⟨TensorProduct.liftAddHom f fun r n x => ?_, fun n x => ?_⟩
  · exact mPt_smul p E E' e r (by rw [map_smul, Algebra.smul_def]) (ha n) (hb n) (ha _) (hb _) j x
  · exact TensorProduct.liftAddHom_tmul _ _ _ _

end HAdd

end GlobalTheory.CompanionTheory.LocBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumToAcrTeichmuller
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LcNatProof

theorem natCast_val_castHom {R : Type} [CommRing R] (l n : ℕ) [NeZero (l ^ n)] [NeZero (l ^ (n + 1))]
    (h : (l : R) ^ n = 0) (a : ZMod (l ^ (n + 1))) :
    (((ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))) a).val : R) = (a.val : R) := by
  have key : (((ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))) a).val : ZMod (l ^ n)) =
      (a.val : ZMod (l ^ n)) := by
    rw [ZMod.natCast_zmod_val, ← map_natCast (ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))),
      ZMod.natCast_zmod_val]
  obtain ⟨c, hc⟩ := Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 key)
  have e := congrArg (Int.cast : ℤ → R) hc
  push_cast at e
  rw [h, zero_mul, sub_eq_zero] at e
  exact e.symm

variable {l : ℕ} [Fact l.Prime]

theorem sum_toAcr_teichmuller (A : PAlg l) {ι : Type} [Fintype ι] {e : ι → A.A}
    (he : CompleteOrthogonalIdempotents e) (n : ℕ) :
    ∑ a, A.toAcr n (WittVector.teichmuller l (e a)) = 1 := by
  have hO : OrthogonalIdempotents (fun a => (WittVector.teichmuller l (e a) : A.W)) :=
    { idem := fun a => by
        change WittVector.teichmuller l (e a) * WittVector.teichmuller l (e a) = WittVector.teichmuller l (e a)
        rw [← map_mul, (he.idem a).eq]
      ortho := fun i j hij => by
        change WittVector.teichmuller l (e i) * WittVector.teichmuller l (e j) = 0
        rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero] }
  have hE : IsIdempotentElem (∑ a, (WittVector.teichmuller l (e a) : A.W)) := hO.isIdempotentElem_sum
  have hu : IsIdempotentElem (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)) := hE.one_sub
  have hc : (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)).coeff 0 = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← WittVector.constantCoeff_apply, map_sub, map_one, map_sum]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [he.complete, sub_self]
  obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff _).2 hc)
  have ht : IsIdempotentElem (A.toAcr n (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W))) := hu.map (A.toAcr n)
  have h0 : A.toAcr n (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)) = 0 := by
    rw [← ht.pow_succ_eq n, ← hc', map_mul, map_natCast, mul_pow, pow_succ (l : A.Acr n) n, A.pow_l_acr n,
      zero_mul, mul_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_one, map_sum, sub_eq_zero] at h0
  exact h0.symm

theorem lcNat : LcIdem → LcSpec → LcNat := by
  intro hId hSp l _ H A hA n
  refine ⟨?_, ?_⟩
  · intro B hB φ h g hg f
    obtain ⟨e, he, hcut, -⟩ := hId l H A hA (ZMod (l ^ n)) f
    have h1 := (hSp l H A hA n).2.2.2 f e he (fun a p => (hcut a p).1)
    have hφ : CompleteOrthogonalIdempotents (φ ∘ e) := he.map φ
    have h2 := (hSp l H B hB n).2.2.2 (lcRes _ (Spec.map (CommRingCat.ofHom g)) f) (φ ∘ e) hφ (fun a p hp => by
      refine (hcut a (PrimeSpectrum.comap g p)).1 fun hm => hp ?_
      have := hg (e a) (he.idem a)
      change algebraMap B.U B.Ug (B.sharp (φ (e a))) ∈ p.asIdeal
      rw [← this]
      exact hm)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, h2, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, PAlg.PdOk.acr_toAcr, WittVector.map_teichmuller, map_natCast]
    rfl
  · intro f
    obtain ⟨e, he, hcut, -⟩ := hId l H A hA (ZMod (l ^ (n + 1))) f
    have h1 := (hSp l H A hA (n + 1)).2.2.2 f e he (fun a p => (hcut a p).1)
    set c := ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n)) with hcdef
    have hL := (hSp l H A hA n).1 (f.map c)
    have hT : ∀ a, A.toAcr n (WittVector.teichmuller l (e a)) * lcA A n (f.map c) =
        A.toAcr n (WittVector.teichmuller l (e a)) * (a.val : A.Acr n) := fun a => by
      rw [hL (e a) (c a) (he.idem a) (fun p hp => by
        change c (f p) = c a
        rw [(hcut a p).1 hp]), natCast_val_castHom l n (A.pow_l_acr n) a]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum, ← one_mul (lcA A n (f.map c)), ← sum_toAcr_teichmuller A he n, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hT a, map_mul, map_natCast]
    rfl

end GlobalTheory.CompanionTheory.LcNatProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwUgCompAlgebraMap
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.TwUg

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem twUg_map (σ : Gal(PadicAlgCl l/K)) {A B : PAlg l} (f : A ⟶ B) :
    (twUg σ B).comp (PAlg.mapUg (PAlg.twMap σ f)) = (PAlg.mapUg f).comp (twUg σ A) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (l : (PAlg.tw σ A).U)) (RingHom.ext fun x => ?_)
  change twUg σ B (PAlg.mapUg (PAlg.twMap σ f) (algebraMap _ _ x)) = PAlg.mapUg f (twUg σ A (algebraMap _ _ x))
  rw [PAlg.mapUg_algebraMap, twUg_algebraMap, twUg_algebraMap, PAlg.mapUg_algebraMap, PAlg.twU_mapU]

theorem twUg_cToUg (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (x : ℂ_[l]) :
    twUg σ A ((PAlg.tw σ A).cToUg x) = A.cToUg (galCp σ x) := by
  have h : ((twUg σ A).comp (PAlg.tw σ A).cToUg).comp
        ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l : Localization.Away (l : OC l) →+* ℂ_[l])) =
      (A.cToUg.comp (galCp σ : ℂ_[l] →+* ℂ_[l])).comp ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l : Localization.Away (l : OC l) →+* ℂ_[l])) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (l : OC l)) (RingHom.ext fun y => ?_)
    have e : (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y) = (y : ℂ_[l]) :=
      (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).commutes y
    have e2 : ((galOC σ y : OC l) : ℂ_[l]) = galCp σ (y : ℂ_[l]) := rfl
    change twUg σ A ((PAlg.tw σ A).cToUg ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y))) =
      A.cToUg (galCp σ ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y)))
    rw [e, PAlg.cToUg_coe, twUg_algebraMap, PAlg.twU_oC, ← e2, PAlg.cToUg_coe]
  obtain ⟨y, rfl⟩ := (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).surjective x
  exact RingHom.congr_fun h y

theorem twUg_kb (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (x : PadicAlgCl l) :
    twUg σ A (kb (PAlg.tw σ A) x) = kb A (σ x) := by
  change twUg σ A ((PAlg.tw σ A).cToUg (clToC l x)) = A.cToUg (clToC l (σ x))
  rw [twUg_cToUg]
  exact congrArg A.cToUg (galCp_coe σ x)

theorem twUg_comp_algebraMap (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) :
    ((twUg σ A).comp (algebraMap (PAlg.tw σ A).U (PAlg.tw σ A).Ug)).comp (PAlg.twUEquiv σ A).symm.toRingHom =
      algebraMap A.U A.Ug := by
  refine RingHom.ext fun x => ?_
  change twUg σ A (algebraMap _ _ ((PAlg.twUEquiv σ A).symm x)) = algebraMap A.U A.Ug x
  rw [twUg_algebraMap]
  exact congrArg (algebraMap A.U A.Ug) ((PAlg.twUEquiv σ A).apply_symm_apply x)

theorem geomPt_galMap (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (y : M.P.obj A) :
    geomPt M A y ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ =
      Spec.map (CommRingCat.ofHom (twUg σ A)) ≫
        geomPt M (PAlg.tw σ A) ((pxTw M.p (okToOC l K) σ (galOC_okToOC σ)).app A y) := by
  refine gb_ext M ?_ ?_
  · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_fst_assoc, geomPt_fst, geomPt_fst]
    change _ = _ ≫ _ ≫ Spec.map (CommRingCat.ofHom (PAlg.twUEquiv σ A).symm.toRingHom) ≫ y.1
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, twUg_comp_algebraMap]
  · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_snd, geomPt_snd, ← Category.assoc, geomPt_snd,
      ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext fun x => twUg_kb σ A x).symm

end GlobalTheory.CompanionTheory.TwUg

theorem GlobalTheory.CompanionTheory.TwUg.twUg_prop : CrystallineSemistableComparison.E.TwUg := fun _ _ _ σ =>
  ⟨fun _ _ f => GlobalTheory.CompanionTheory.TwUg.twUg_map σ f, fun A x => GlobalTheory.CompanionTheory.TwUg.twUg_kb σ A x,
    fun M A y => GlobalTheory.CompanionTheory.TwUg.geomPt_galMap M σ A y⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltIterateSymmEpsilon
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EpsRootProof

variable {l : ℕ} [hl : Fact l.Prime]

theorem iterate_symm_ofCompatible (y : ℕ → OC l) (hy : ∀ k, y (k + 1) ^ l = y k) (n : ℕ) :
    ((_root_.frobeniusEquiv (Ob l) l).symm^[n]) (IsPerfectoidField.ofCompatible l y hy) =
      IsPerfectoidField.ofCompatible l (fun k => y (k + n))
        (fun k => by rw [show k + 1 + n = (k + n) + 1 by omega]; exact hy (k + n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, AInf.frobeniusEquiv_symm_ofCompatible]
    congr 1
    funext k
    exact congrArg y (by omega)

theorem iterate_symm_pow (x : Ob l) (n : ℕ) :
    (((_root_.frobeniusEquiv (Ob l) l).symm^[n]) x) ^ l ^ n = x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p, ih]

theorem untilt_iterate_symm_epsilon (n : ℕ) :
    PreTilt.untilt (((_root_.frobeniusEquiv (Ob l) l).symm^[n]) (epsilon l)) = rootSeqInt l n := by
  rw [epsilon, iterate_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible, zero_add]

theorem sharp_s_eq_oC_untilt (A : PAlg l) (x : Ob l) : A.sharp (A.s x) = A.oC (PreTilt.untilt x) := by
  have h : WittVector.teichmuller l (A.s x) = A.sW (WittVector.teichmuller l x) :=
    (WittVector.map_teichmuller l A.s x).symm
  change A.th (WittVector.teichmuller l (A.s x)) = _
  rw [h, ← PAlg.oC_theta0]
  exact congrArg A.oC (WittVector.fontaineTheta_teichmuller _)

theorem epsRoot : CrystallineSemistableComparison.E.EpsRoot := by
  intro l _ n
  exact ⟨((_root_.frobeniusEquiv (Ob l) l).symm^[n]) (epsilon l), iterate_symm_pow _ n, fun A => by
    rw [sharp_s_eq_oC_untilt, untilt_iterate_symm_epsilon]⟩

end GlobalTheory.CompanionTheory.EpsRootProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VnRed
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.FUntwPf

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def vn (E : Spc) (k : ℕ) (a : Ht (l ^ k) E ((2 : ℕ) : ℤ) 1) (b : Ht (l ^ k) E ((0 : ℕ) : ℤ) (-1)) : Ht (l ^ k) E ((2 : ℕ) : ℤ) 0 :=
  (cup (l ^ k) a b).cast rfl rfl

theorem vn_red (h : A11) (E : Spc) (k : ℕ) (a : Ht (l ^ (k + 1)) E ((2 : ℕ) : ℤ) 1) (b : Ht (l ^ (k + 1)) E ((0 : ℕ) : ℤ) (-1)) :
    red (l ^ (k + 1)) (l ^ k) E ((2 : ℕ) : ℤ) 0 (vn E (k + 1) a b) =
      vn E k (red (l ^ (k + 1)) (l ^ k) E _ _ a) (red (l ^ (k + 1)) (l ^ k) E _ _ b) := by
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact (h (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l k.le_succ) E).1 a b

theorem step (hF : FCup) (hO : CupOne) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ)
    (a : Ht (l ^ n) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1) (b : Ht (l ^ n) (sch.obj (gb M)) ((0 : ℕ) : ℤ) (-1))
    (hb : eM hN H r M n (-1) 0 b = oneH (AcrEl M.P n)) :
    eM hN H r M n 0 2 (vn (sch.obj (gb M)) n a b) = eM hN H r M n 1 2 a := by
  have h := hF E hN l H r K M n 1 (-1) 0 rfl 2 0 2 rfl a b
  have h2 := congrArg ((mulP (AcrEl M.P n)).cup (add_zero 2) (eM hN H r M n 1 2 a)) hb
  have h' : (mulP (AcrEl M.P n)).cup (add_zero 2) (eM hN H r M n 1 2 a) (oneH (AcrEl M.P n)) = eM hN H r M n 1 2 a :=
    hO _ _ _ _ _
  exact h.trans (h2.trans h')

theorem core (E : EtIn) (hF : FCup) (hO : CupOne) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K)
    (x : Hl l (sch.obj (gb M)) (2 : ℕ) 1) (w : Hl l (sch.obj (gb M)) (0 : ℕ) (-1))
    (hw : ∀ n, eM hN H r M n (-1) 0 (w.1 n) = oneH (AcrEl M.P n)) :
    ∃ v : Hl l (sch.obj (gb M)) (2 : ℕ) 0, ∀ n, eM hN H r M n 0 2 (v.1 n) = eM hN H r M n 1 2 (x.1 n) := by
  have hv : ∀ k, red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 0
      (vn (sch.obj (gb M)) (k + 1) (x.1 (k + 1)) (w.1 (k + 1))) = vn (sch.obj (gb M)) k (x.1 k) (w.1 k) := by
    intro k
    have h1 : red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1 (x.1 (k + 1)) = x.1 k := x.2 k
    have h2 : red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((0 : ℕ) : ℤ) (-1) (w.1 (k + 1)) = w.1 k := w.2 k
    exact (vn_red E.a11 _ k _ _).trans (congrArg₂ (vn (sch.obj (gb M)) k) h1 h2)
  exact ⟨⟨fun k => vn (sch.obj (gb M)) k (x.1 k) (w.1 k), hv⟩, fun n => step hF hO E hN H r M n (x.1 n) (w.1 n) (hw n)⟩

theorem main : CrystallineSemistableComparison.E.FCup → CrystallineSemistableComparison.E.FRoot → CrystallineSemistableComparison.E.CupOne → CrystallineSemistableComparison.E.FUntw :=
  fun hF hR hO E hN l _ H r K M x => (hR E hN l H r K M (-1)).elim fun w hw => core E hF hO hN H r M x w hw

end GlobalTheory.CompanionTheory.FUntwPf
end
end

