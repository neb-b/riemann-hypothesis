module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.HermitianCurvature.StatementMA
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
public import Formalism.HermitianCurvature.StatementM
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
public import Formalism.HermitianCurvature.StatementB

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDifferentialLattice
section
open NumberField in
private theorem UpperTheory.Reformulated.B.ExistsNatMultipleBasisVectorMemLattice.aux {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V)
    (h : Submodule.span E (L : Set V) = ⊤) (x : V) : ∃ d : ℕ, 0 < d ∧ (d : E) • x ∈ L := by
  obtain ⟨⟨t, m, hm, rfl⟩, ht⟩ := multiple_mem_span_of_mem_localization_span
    (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) E (L : Set V) x (h ▸ Submodule.mem_top)
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  have h1 : m • x ∈ L := by simpa [Submonoid.smul_def, Int.cast_smul_eq_zsmul] using ht
  refine ⟨(m * m).toNat, by have := mul_self_pos.mpr hm0; omega, ?_⟩
  rw [Nat.cast_smul_eq_nsmul, ← natCast_zsmul, Int.toNat_of_nonneg (mul_self_nonneg m), mul_smul]
  exact L.smul_of_tower_mem m h1

theorem UpperTheory.Reformulated.B.ExistsNatMultipleBasisVectorMemLattice.exists_dL :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    ∃ (dL : ℕ),
      (0 : ℕ) < dL ∧
        ∀ (i : Fin X.B.I.n),
          (↑dL : X.B.I.E) • Pi.single i (1 : X.B.I.E) ∈
            X.B.I.L := by
  intro D X
  choose d hd hL using fun i : Fin X.B.I.n =>
    UpperTheory.Reformulated.B.ExistsNatMultipleBasisVectorMemLattice.aux X.B.I.L X.B.I.L_span (Pi.single i (1 : X.B.I.E))
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  rw [hc, mul_comm, Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
  exact X.B.I.L.smul_of_tower_mem c (hL i)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntertwinerStructure
section
noncomputable def UpperTheory.Reformulated.B.IntertwinerStructure.Intw :
    {Wp Wq : Type} →
      [inst : NormedAddCommGroup Wp] →
        [inst_1 : InnerProductSpace ℂ Wp] →
          [inst_2 : NormedAddCommGroup Wq] →
            [inst_3 : InnerProductSpace ℂ Wq] →
              [FiniteDimensional ℂ Wq] →
                (P : Formalism.FourierDecayAlt.M.Par) →
                  (Bs : Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq) →
                    (Formalism.FourierDecayAlt.M.Ty P → ℂ → Wq →L[ℂ] Wp) →
                      Formalism.FourierDecayAlt.Q.Pr ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') →
                        Formalism.FourierDecayAlt.MA.A P (Formalism.FourierDecayAlt.MA.DQ P) → Prop :=
    fun {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
        [FiniteDimensional ℂ Wq] (P : Formalism.FourierDecayAlt.M.Par) (Bs : Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq)
        (e : Formalism.FourierDecayAlt.M.Ty P → ℂ → Wq →L[ℂ] Wp) (A : Formalism.FourierDecayAlt.Q.Pr ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
        (A' : Formalism.FourierDecayAlt.MA.A P (Formalism.FourierDecayAlt.MA.DQ P)) ↦
      ∀ (Φ : ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')),
        Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR P Bs e
                  ((A.1 : ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') → ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
                    Φ) =
          Formalism.FourierDecayAlt.MA.actA P A' (Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR P Bs e Φ)

theorem UpperTheory.Reformulated.B.IntertwinerStructure.intw_sum :
    ∀ {Wp Wq : Type} [inst : NormedAddCommGroup Wp] [inst_1 : InnerProductSpace ℂ Wp] [inst_2 : NormedAddCommGroup Wq]
      [inst_3 : InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [inst_5 : FiniteDimensional ℂ Wq] {P : Formalism.FourierDecayAlt.M.Par}
      {Bs : Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq} {e : Formalism.FourierDecayAlt.M.Ty P → ℂ → Wq →L[ℂ] Wp},
      (∀ (Φ : ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (ρ : Formalism.FourierDecayAlt.M.Ty P),
          Formalism.FourierDecayAlt.P.CutMP.Gauge.rawR P Bs.μsec e (↑Φ : Formalism.FourierDecayAlt.Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ ∈
            Formalism.FourierDecayAlt.MA.smSub P.r P.TT) →
        ∀ {ι : Type} (s : Finset ι) {A : ι → Formalism.FourierDecayAlt.Q.Pr ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
          {A' : ι → Formalism.FourierDecayAlt.MA.A P (Formalism.FourierDecayAlt.MA.DQ P)},
          (∀ i ∈ s, UpperTheory.Reformulated.B.IntertwinerStructure.Intw P Bs e (A i) (A' i)) → UpperTheory.Reformulated.B.IntertwinerStructure.Intw P Bs e (∑ i ∈ s, A i) (∑ i ∈ s, A' i) := by
  intro Wp Wq _ _ _ _ _ _ P Bs e hs ι s A A' h
  have hv : ∀ Φ ρ q, (Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR P Bs e Φ ρ).1 q =
      Formalism.FourierDecayAlt.P.CutMP.Gauge.rawR P Bs.μsec e Φ.1 ρ q := fun Φ ρ q => by
    simp only [Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR, Formalism.FourierDecayAlt.MA.toSm, dif_pos (hs Φ ρ)]
  have hh : ∀ X Y : Wq →L[ℂ] Wp, Formalism.FourierDecayAlt.B.hsVec (X + Y) = Formalism.FourierDecayAlt.B.hsVec X + Formalism.FourierDecayAlt.B.hsVec Y := fun _ _ => rfl
  let T : _ →+ _ := AddMonoidHom.mk' (Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR P Bs e) fun Φ Ψ => funext fun ρ => Subtype.ext <|
    funext fun q => (hv _ ρ q).trans <| Eq.trans (by simp [Formalism.FourierDecayAlt.P.CutMP.Gauge.rawR, hh, inner_add_right, mul_add])
      (congrArg₂ (· + ·) (hv Φ ρ q) (hv Ψ ρ q)).symm
  refine Finset.sum_induction (p := fun x : _ × _ => UpperTheory.Reformulated.B.IntertwinerStructure.Intw P Bs e x.1 x.2) (fun i => (A i, A' i))
    (fun a b ha hb Φ => (T.map_add _ _).trans ((congrArg₂ (· + ·) (ha Φ) (hb Φ)).trans
      (funext fun ρ => Finset.sum_add_distrib.symm)))
    (fun Φ => T.map_zero.trans (funext fun ρ => Finset.sum_const_zero.symm)) h |> fun H => ?_
  simpa only [Prod.fst_sum, Prod.snd_sum] using H
end

