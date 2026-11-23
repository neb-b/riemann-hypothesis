module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0269
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Formalism.LocalToGlobal.Columns.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0004
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPStepCIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0270

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealSubfieldHeckeCharFinitePartEqOne
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj finiteCompletionMap)

namespace GlobalTheory.HeckeFinTriv

theorem valued_natCast_le_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v (n : v.adicCompletion K) ≤ 1 := by
  induction n with
  | zero => rw [Nat.cast_zero, map_zero]; exact zero_le
  | succ n ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (by rw [map_one])

theorem valued_natCast_le_of_dvd {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {M N : ℕ}
    (h : M ∣ N) : Valued.v (N : v.adicCompletion K) ≤ Valued.v (M : v.adicCompletion K) := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_le_of_le_one_right' (valued_natCast_le_one v k)

theorem finPart_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : HChar (maximalRealSubfield E)) (M : ℕ), (∀ a : Ideles (maximalRealSubfield E), a ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) → (∀ w, (a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v ((a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 P - 1) ≤ Valued.v ((M : maximalRealSubfield E) : P.adicCompletion (maximalRealSubfield E))) → ψ.1 a = 1) → (∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → ψ.UnrAt (w.under (𝓞 (maximalRealSubfield E)))) → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (N : ℕ), M ∣ N → ∀ b : Ideles (maximalRealSubfield E), ideleMap (maximalRealSubfield E) E b ∈ levT E {w | GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀} N → ψ.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b) = 1 := by
  intro E _ _ _ ψ M hlev hns w₀ N hMN b hb
  have he : ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal ≠ 0 := fun w =>
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 (maximalRealSubfield E))).ne_bot
  have hc : ∀ w : HeightOneSpectrum (𝓞 E), (ideleMap (maximalRealSubfield E) E b).val.2 w =
      finiteCompletionMap (maximalRealSubfield E) E w (b.val.2 (w.under (𝓞 (maximalRealSubfield E)))) := fun w => rfl
  have hs : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) = v := fun v => by
    haveI := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
    exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩

  have hunit : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v (b.val.2 v) = 1 := fun v => by
    obtain ⟨w, rfl⟩ := hs v
    have h := hb.1 w
    change Valued.v ((ideleMap (maximalRealSubfield E) E b).val.2 w) = 1 at h
    rw [hc, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, pow_eq_one_iff_of_nonneg zero_le (he w)] at h
    exact h

  have hcong : ∀ w : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w → w ≠ w₀ →
      Valued.v (b.val.2 (w.under (𝓞 (maximalRealSubfield E))) - 1) ≤ Valued.v (N : (w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := fun w h1 h2 => by
    have h := hb.2 w ⟨h1, h2⟩
    change Valued.v ((ideleMap (maximalRealSubfield E) E b).val.2 w - 1) ≤ _ at h
    rwa [hc, ← map_one (finiteCompletionMap (maximalRealSubfield E) E w), ← map_sub, ← map_natCast (finiteCompletionMap (maximalRealSubfield E) E w),
      GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap,
      pow_le_pow_iff_left₀ zero_le zero_le (he w)] at h
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local (maximalRealSubfield E) ψ.1 ψ.2.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b)
    (GlobalTheory.Mem.Chr.finPartI_mem_unitIdl.2 hunit) (fun w => by rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl) ?_
  intro v x hx
  rw [GlobalTheory.Mem.Chr.finPartI_snd] at hx
  have hxu : Valued.v (x : v.adicCompletion (maximalRealSubfield E)) = 1 := by rw [hx]; exact hunit v
  by_cases hu : ψ.UnrAt v
  · exact hu x hxu
  obtain ⟨w, hw⟩ := hs v
  have hsp : GlobalTheory.UnitaryBC.IsSplitAt w := by
    by_contra hn
    exact hu (hw ▸ hns w hn)
  obtain ⟨u, hu1, hu2⟩ := hsp
  have hsp' : ∃ w' : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w' ∧ w' ≠ w₀ ∧ w'.under (𝓞 (maximalRealSubfield E)) = v := by
    by_cases h0 : w = w₀
    · refine ⟨u, ⟨w, fun e => hu1 e.symm, hu2.symm⟩, h0 ▸ hu1, hu2.trans hw⟩
    · exact ⟨w, ⟨u, hu1, hu2⟩, h0, hw⟩
  obtain ⟨w', hw'1, hw'2, rfl⟩ := hsp'
  have hxc : Valued.v ((x : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) - 1) ≤
      Valued.v ((M : (maximalRealSubfield E)) : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := by
    rw [hx]
    refine (hcong w' hw'1 hw'2).trans ?_
    have e : ((M : (maximalRealSubfield E)) : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) = (M : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := by
      rw [← map_natCast (algebraMap (maximalRealSubfield E) ((w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E))) M]; rfl
    rw [e]
    exact valued_natCast_le_of_dvd _ hMN
  apply hlev
  · intro P
    by_cases hP : P = w'.under (𝓞 (maximalRealSubfield E))
    · subst hP
      rw [GlobalTheory.HeckeProduct.localIdele_snd_self]
      exact hxu
    · rw [GlobalTheory.HeckeProduct.localIdele_snd_ne (maximalRealSubfield E) _ _ hP]
      exact map_one _
  · intro w
    rw [GlobalTheory.HeckeProduct.localIdele_fst]
    rfl
  · intro P
    by_cases hP : P = w'.under (𝓞 (maximalRealSubfield E))
    · subst hP
      rw [GlobalTheory.HeckeProduct.localIdele_snd_self]
      exact hxc
    · rw [GlobalTheory.HeckeProduct.localIdele_snd_ne (maximalRealSubfield E) _ _ hP, sub_self, map_zero]
      exact zero_le

end GlobalTheory.HeckeFinTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsMatchPeriodMapOfFurtherProperties
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.KerRat GlobalTheory.Mem.Df GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped Matrix

namespace GlobalTheory.AtG.RX

section Fam
variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (R3.Gc X.B px → X.B.LL))
  (tr : R3.TrI X.B px) (a : I.ι)


set_option maxHeartbeats 1000000 in
theorem isFormOf_exists (z : MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) :
    ∃ y, IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y) := by
  have hK := mtildeKOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX
  obtain ⟨hφ, -⟩ := (mem_MtildeV_iff (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) z.1).1 z.2
  let F : (mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a)).EqFun := ⟨z.1, hφ⟩
  have h1 := (mem_lvlPartX_iff (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hK F).2 z.2
  rw [← LiftForms.range_lvlE] at h1
  obtain ⟨y, hy⟩ := h1
  refine ⟨y, F, z.2, ?_, rfl⟩
  apply heq_of_eq
  show _ = (MtildeKCSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hK).basis.equivFun.symm
    ((MtildeKCSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hK).lvlE _ _ _ *ᵥ y)
  rw [Matrix.mulVecLin_apply] at hy
  rw [hy]
  exact ((MtildeKCSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hK).basis.equivFun.symm_apply_apply _).symm

theorem isFormOf_unique {y} {z z' : MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)}
    (h : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y))
    (h' : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z'
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y)) : z = z' := by
  obtain ⟨F, hF, e1, rfl⟩ := h
  obtain ⟨F', hF', e2, rfl⟩ := h'
  have e3 := eq_of_heq (e1.trans e2.symm)
  have e4 := ((mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a)).res _).injective e3
  subst e4
  rfl


set_option maxHeartbeats 1000000 in
theorem isFormOf_mem_iff {y} {z : MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)}
    (h : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y)) :
    y ∈ rNab X.toD7 (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) ↔
      z ∈ MtildeL (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) := by
  obtain ⟨F, hF, e1, rfl⟩ := h
  have e2 := eq_of_heq e1
  refine (LiftForms.mem_lvlNab _ _ _ _ y).trans ?_
  show R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y ∈ intForms _ ↔ _
  rw [← e2]
  exact (GSD.mem_intNab_iff _ (mtildeKOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX) _ F).symm

end Fam

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0}

theorem lat_of_rx (x : RXs t) (a : w.C.Tup) :
    (∀ v ∈ (Z.W.Mtilde a).gen, ∃ z, x.e a (toCx w.I t.hX a z) = v) ∧
    ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (w.I.tup a) (TC.Ps w.I) ↔ ∃ c : Z.W.Amb a → 𝓞 B.LL,
      x.e a (toCx w.I t.hX a z) = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v := by
  classical
  obtain ⟨hg, hiff⟩ := x.all.latA a
  have hc := x.crd a
  refine ⟨fun v hv => ?_, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := hg v hv
    obtain ⟨z, -, hz⟩ := hc y
    exact ⟨z, hz.symm⟩
  · obtain ⟨y, hy⟩ := isFormOf_exists (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a z
    obtain ⟨z', hz', hj⟩ := hc y
    have e := isFormOf_unique (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a hy hz'
    obtain ⟨c, hc'⟩ := (hiff y).1 ((isFormOf_mem_iff (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a hy).2 hz)
    exact ⟨c, by rw [e, ← hj]; exact hc'⟩
  · rintro ⟨c, hc'⟩
    choose! g hgy using hg
    let n := rDim (w.st Z).toD7 (famAll t) (R3.lev1 w.I) (R3.chr1 w.I) (tAll w.I a)
    let y : Fin n → B.LL := ∑ v ∈ (Z.W.Mtilde a).gen, ((c v : 𝓞 B.LL) : B.LL) • @id (Fin n → B.LL) (g v)
    have hjy : x.all.jA a y = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v := by
      let J : (Fin n → B.LL) →ₛₗ[B.embLL] Z.W.Amb a := x.all.jA a
      refine (map_sum J _ _).trans (Finset.sum_congr rfl fun v hv => ?_)
      exact (J.map_smulₛₗ _ _).trans (congrArg _ (hgy v hv))
    obtain ⟨z', hz', hj⟩ := hc y
    have e : z' = z := by
      apply toMtilde_injective (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (w.I.tup a) (TC.Ps w.I) B.embLL
      apply (x.e a).injective
      exact hj.symm.trans (hjy.trans hc'.symm)
    rw [← e]
    exact (isFormOf_mem_iff (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a hz').1 ((hiff y).2 ⟨c, hjy⟩)

section Core

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (hX : B.fields.Ok)

theorem eq_rowForm' (u : B.Word) (a : I.ι) (z : MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) (G : (I.per l u a).Mt)
    (hG : SameForm I l u a (toCx I hX a z) G) : G = rowForm I l h u a z :=
  Subtype.ext (funext fun _ => funext fun p => hG p)

theorem rowPin_core (Z : TC.Later B (I.cols l)) (e0 : ∀ a : (I.cols l).Tup, MtCx I a ≃ₗ[ℂ] Z.W.Amb a)
    (u : B.Word) (a : (I.cols l).Tup) (e : (I.per l u a).Mt ≃ₗ[ℂ] Z.W.Amb a)
    (he : ∀ F, SameForm I l u a F (e.symm (e0 a F)))
    (hgen : ∀ v ∈ (Z.W.Mtilde a).gen, ∃ z, e0 a (toCx I hX a z) = v)
    (hlat : ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps ↔ ∃ c : Z.W.Amb a → 𝓞 B.LL,
      e0 a (toCx I hX a z) = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v) :
    (∀ v ∈ (Z.W.Mtilde a).gen, ∃ z, e (rowForm I l h u a z) = v) ∧
    ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps ↔ ∃ c : Z.W.Amb a → 𝓞 B.LL,
      e (rowForm I l h u a z) = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v := by
  have key : ∀ z, e (rowForm I l h u a z) = e0 a (toCx I hX a z) := fun z => by
    rw [← eq_rowForm' I h l hX u a z _ (he _)]
    exact e.apply_symm_apply _
  refine ⟨fun v hv => ?_, fun z => ?_⟩
  · obtain ⟨x, hx⟩ := hgen v hv
    exact ⟨x, (key x).trans hx⟩
  · rw [key]
    exact hlat z

end Core

theorem rowPin_of_rx : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0), RX K B f T w Z Wt p0 t → ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a := by
  intro K B f T w Z Wt p0 t x a u
  obtain ⟨hg, hl⟩ := lat_of_rx (t := t) x a
  by_cases ha : a = (w.D Z).what₂.mu0
  · subst ha
    exact ⟨Z.W.eMt0 u, fun _ => HEq.rfl, fun hn => absurd rfl hn,
      rowPin_core w.I w.ok w.l t.hX Z x.e u _ (Z.W.eMt0 u) (x.eMt0 u) hg hl⟩
  · exact ⟨Z.W.eMtTw u a, fun hn => absurd hn ha, fun _ => rfl,
      rowPin_core w.I w.ok w.l t.hX Z x.e u a (Z.W.eMtTw u a) (x.eMtTw u a) hg hl⟩

end GlobalTheory.AtG.RX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnPeriodLatticeVacuumSmooth
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem laHyp_eSmooth_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (a : I.ι) (u : B.Word) (i : ℕ), i < B.R.m →
      I.A.LaHyp (B.R.N i) (B.R.N (i + 1)) (ColIn.Sb I a u) ∧ I.A.ESmooth (B.R.N i) (B.R.N (i + 1)) := by
  intro B X I h _ l Z a u i _
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have he : ∀ k, Even (B.R.N k) := fun k => Formalism.L2.Ker.even_rankN B.R k
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem
  have hδ := ((I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok).1
  have hs := seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G
  have hL := Formalism.L2.Ker.laHyp_ambOf_top (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
    hs hδ (he i) (he (i + 1)) ∅ (fun P hP => absurd hP (Finset.notMem_empty P)) (fun P hP => absurd hP (Finset.notMem_empty P))
  have hcc : TaylorLogMetric.IsCurveIdeal (assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ := ⟨top_ne_bot, by simp⟩
  have hE := Formalism.L2.Ker.Cd.ambOf_eSmooth (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar
    I.chi I.J.cD hs hcc hδ I.J.δ_ne_zero (he i) (he (i + 1))
  rw [ColIn.A, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
  exact ⟨⟨hL.1, hL.2.1, fun P hP => (bad P hP).1, fun P hP => GlobalTheory.PeriodIdealUnit.locP_AA_eq_one _ _ _ _ _ _ _ _ P (bad P hP).2.1
    (bad P hP).2.2.1 (by simp), hL.2.2.2.2⟩, hE⟩

end GlobalTheory.Mem.Col2.TC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesLocalModelsOfOtherDivisionLatticesHeights
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd


set_option maxHeartbeats 800000 in
theorem modelsAt_tr : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    ModelsAt D O → ModelsAt (setDiv D N h) (O.tr N h) := by
  intro D O N h H hT hk
  obtain ⟨h0, LC, hLC⟩ := H hT hk
  refine ⟨h0, LC, fun μ hμ u w hg hq => ?_⟩
  obtain ⟨c1, c2⟩ := hLC μ hμ u w hg hq
  exact ⟨_root_.GlobalTheory.Svd.cmpLite_setDiv D N h _ _ u μ w hg _ _ _ c1, _root_.GlobalTheory.TwU.siteAdm_setDiv D N h u w hg _ _ _ c2⟩

end GlobalTheory.Svd
end

