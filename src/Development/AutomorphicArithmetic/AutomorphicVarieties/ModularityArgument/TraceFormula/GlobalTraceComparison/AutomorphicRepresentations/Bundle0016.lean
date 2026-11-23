module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0007
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0008
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0304

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PartEq
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open scoped Classical ENNReal

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

private theorem row_int (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) (w : Lp ℂ 2 D.ν) (x : H E n 0) :
    Integrable (fun y => kerH φ x y * (w : H E n 0 → ℂ) y) D.ν :=
  by
    let X : Ctx := by
      haveI := CuspidalL2GL.t2Space_GA E n
      haveI := CuspidalL2GL.t2Space_GA E 0
      haveI := CuspidalL2GL.locallyCompactSpace_GA E n
      haveI := CuspidalL2GL.locallyCompactSpace_GA E 0
      haveI := CuspidalL2GL.secondCountableTopology_GA E n
      haveI := CuspidalL2GL.secondCountableTopology_GA E 0
      haveI := (ratProper_holds E n).2.1
      haveI := (ratProper_holds E 0).2.1
      refine { G := H E n 0
               ms := borelH E n 0
               bs := ⟨rfl⟩
               μ := D.μ
               haar := { toIsFiniteMeasureOnCompacts := @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ D.μ D.haar.2.2.2, toIsMulLeftInvariant := D.haar.1, toIsOpenPosMeasure := D.haar.2.2.1 }
               Γ := ratH E n 0
               cn := (((ratGL E n).prodMap (ratGL E 0)).rangeRestrict_surjective).countable
               proper := ?_
               F := D.F
               fd := D.fd }
      intro C hC
      have h1 := (ratProper_holds E n).2.2 _ (hC.image continuous_fst)
      have h2 := (ratProper_holds E 0).2.2 _ (hC.image continuous_snd)
      refine ((h1.prod h2).image ((ratGL E n).prodMap (ratGL E 0)).rangeRestrict).subset ?_
      rintro ⟨_, γ, rfl⟩ hγ
      exact ⟨γ, ⟨⟨_, hγ, rfl⟩, ⟨_, hγ, rfl⟩⟩, rfl⟩
    exact MemLp.integrable_mul ((kernel_rows_columns_square_integrable X φ hφ).2 x) (Lp.memLp w)

private theorem ker_trM (D : Dom E n 0) {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) (M : Matrix ι ι ℂ)
    (x y : H E n 0) : kerH (trM Φ M) x y = ∑ i, ∑ j, kerH (Φ i j) x y * M j i := by
  let X : Ctx := by
    haveI := CuspidalL2GL.t2Space_GA E n
    haveI := CuspidalL2GL.t2Space_GA E 0
    haveI := CuspidalL2GL.locallyCompactSpace_GA E n
    haveI := CuspidalL2GL.locallyCompactSpace_GA E 0
    haveI := CuspidalL2GL.secondCountableTopology_GA E n
    haveI := CuspidalL2GL.secondCountableTopology_GA E 0
    haveI := (ratProper_holds E n).2.1
    haveI := (ratProper_holds E 0).2.1
    refine { G := H E n 0
             ms := borelH E n 0
             bs := ⟨rfl⟩
             μ := D.μ
             haar := { toIsFiniteMeasureOnCompacts := @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ D.μ D.haar.2.2.2, toIsMulLeftInvariant := D.haar.1, toIsOpenPosMeasure := D.haar.2.2.1 }
             Γ := ratH E n 0
             cn := (((ratGL E n).prodMap (ratGL E 0)).rangeRestrict_surjective).countable
             proper := ?_
             F := D.F
             fd := D.fd }
    intro C hC
    have h1 := (ratProper_holds E n).2.2 _ (hC.image continuous_fst)
    have h2 := (ratProper_holds E 0).2.2 _ (hC.image continuous_snd)
    refine ((h1.prod h2).image ((ratGL E n).prodMap (ratGL E 0)).rangeRestrict).subset ?_
    rintro ⟨_, γ, rfl⟩ hγ
    exact ⟨γ, ⟨⟨_, hγ, rfl⟩, ⟨_, hγ, rfl⟩⟩, rfl⟩
  have h := (kerLin X (ι × ι) (fun p => Φ p.1 p.2) (fun p => M p.2 p.1)
    (fun p => hΦ p.1 p.2)).2 x y
  have e : trM Φ M = fun z => ∑ p : ι × ι, Φ p.1 p.2 z * M p.2 p.1 := by
    funext z
    simp only [trM, Fintype.sum_prod_type]
  rw [e]
  refine Eq.trans h ?_
  exact Fintype.sum_prod_type _

private theorem part_eq {D : Dom E n 0} {π : CuspSub E n} {U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D}
    (h : IsPiPart D π U Uπ) (f : Hs (ι := ι) D) : Uπ f = U ((piSp D π ι).starProjection f) := by
  have h1 : Uπ ((piSp D π ι).starProjection f) = U ((piSp D π ι).starProjection f) :=
    h.1 _ (Submodule.starProjection_apply_mem _ _)
  have h2 : Uπ (f - (piSp D π ι).starProjection f) = 0 :=
    h.2 _ (Submodule.sub_starProjection_mem_orthogonal _)
  rw [map_sub, sub_eq_zero] at h2
  rw [h2, h1]

private theorem vec_int {D : Dom E n 0} (w : Lp ℂ 2 D.ν) (c : ι → ℂ) (j : ι) {φ : H E n 0 → ℂ} (hφ : IsTestH φ)
    (x : H E n 0) :
    ∫ y, kerH φ x y * ((vecM w c) j : H E n 0 → ℂ) y ∂D.ν = c j * ∫ y, kerH φ x y * (w : H E n 0 → ℂ) y ∂D.ν := by
  have e : ((vecM w c) j : H E n 0 → ℂ) =ᵐ[D.ν] fun y => c j * (w : H E n 0 → ℂ) y := by
    have : (vecM w c) j = c j • w := rfl
    rw [this]
    filter_upwards [Lp.coeFn_smul (c j) w] with y hy
    simpa using hy
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [e] with y hy
  rw [hy]; ring

end SlopeTestRemainingChoices

theorem ker_pf :
    Weak → PointRep → PComm → PDiag → Ker := by
  intro hW hPR hPC hPD E _ _ _ n ι _ s m v x
  set w := P0 s.D s.π v with hw
  let u : ι → Hs (ι := ι) s.D := fun i => ContinuousLinearMap.adjoint m.Uπ (s.k₁ x i)
  have hG : ∀ y, (v : H E n 0 → ℂ) y * m.G x (th y) =
      ∑ i, (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i) := by
    intro y
    simp only [Mid.G, Gk, Finset.mul_sum, u, ContinuousLinearMap.adjoint_inner_left]
  have hI : ∀ i, Integrable (fun y => (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i)) s.D.ν :=
    fun i => (hW E n ι s v (u i) i).1
  have hterm : ∀ i, ∫ y, (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i) ∂s.D.ν =
      ∑ j, s.M j i * ∫ y, kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y ∂s.D.ν := by
    intro i
    rw [(hW E n ι s v (u i) i).2]
    have e1 : inner ℂ (u i) (s.T₂ (vecM v fun l => s.M l i)) =
        inner ℂ (s.k₁ x i) (m.U (s.T₂ (vecM w fun l => s.M l i))) := by
      simp only [u, ContinuousLinearMap.adjoint_inner_left]
      rw [part_eq m.pp, hPC E n s.pos s.D s.π s.fix ι s.Φ₂ s.T₂ s.t₂ s.o₂, hPD E n s.D s.π ι]
    rw [e1, hPR E n ι s m.Φ (s.T₁ * m.U * s.T₂) m.t m.o (m.U (s.T₂ (vecM w fun l => s.M l i)))
      (vecM w fun l => s.M l i) rfl x i]
    exact Finset.sum_congr rfl fun j _ => vec_int w _ j (m.t i j) x
  refine ⟨?_, ?_⟩
  · simp only [hG]
    exact integrable_finsetSum _ fun i _ => hI i
  · simp only [hG]
    rw [integral_finsetSum _ fun i _ => hI i]
    simp only [hterm]
    have e2 : ∀ y, kerH m.φ x y * (w : H E n 0 → ℂ) y =
        ∑ i, ∑ j, s.M j i * (kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y) := by
      intro y
      rw [Mid.φ, ker_trM s.D m.t, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [e2]
    have hr : ∀ i j, Integrable (fun y => kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y) s.D.ν :=
      fun i j => row_int s.D (m.t i j) w x
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hr i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hr i j).const_mul _]
    exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PositionPairFunctionsEq
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem tst_trM (D : Dom E n 0) {ι : Type} [Fintype ι] {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ)
    (M : Matrix ι ι ℂ) : PositivityTheory.Rg.BcB.E1.Tst (G := (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D).G) (trM Φ M) := by
  have h := (PositivityTheory.Rg.BcB.E1.kerLin (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) (ι × ι)
    (fun p => Φ p.1 p.2) (fun p => M p.2 p.1) (fun p => hΦ p.1 p.2)).1
  have e : trM Φ M = fun y => ∑ p : ι × ι, Φ p.1 p.2 y * M p.2 p.1 := by
    funext y
    rw [Fintype.sum_prod_type]
    rfl
  rw [e]
  exact h

private theorem cusp_projection_self (D : Dom E n 0) (π : CuspSub E n) {ψ : Sm E n} (hψ : ψ ∈ π.V) {w : ℝ → ℂ}
    (hw : Continuous w) (hws : HasCompactSupport w) (v : Lp ℂ 2 D.ν)
    (hv : (v : H E n 0 → ℂ) =ᵐ[D.ν] fun x => ψ.1 x.1 * w (ldet x)) : P0 D π v = v := by
  have hvec : IsPiVec D π (vecM v fun _ : Unit => (1 : ℂ)) := fun _ => ⟨ψ, hψ, w, hw, hws, by
    have e : (vecM v fun _ : Unit => (1 : ℂ)) () = v := one_smul ℂ v
    simpa [e] using hv⟩
  have hmem : (vecM v fun _ : Unit => (1 : ℂ)) ∈ piSp D π Unit :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span hvec)
  unfold P0
  rw [Submodule.starProjection_eq_self_iff.2 hmem]
  exact one_smul ℂ v

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.rep_pf :
    Basic → ThetaInt → KInv → PDiag → Ker → Rep := by
  intro hB hTI hK _ hKer E _ _ _ n ι _ s m ψ hψ u hu hus x₀
  obtain ⟨-, bMul, -, -, -, -, bThL, bThTh, bThMul, bRat, -, -⟩ := hB E n s.pos
  obtain ⟨ψ₁, hψ₁, hψe⟩ := s.fix.2 ψ hψ
  have hw : Continuous fun t : ℝ => u (-t) := hu.comp continuous_neg
  have hws : HasCompactSupport fun t : ℝ => u (-t) := hus.comp_homeomorph (Homeomorph.neg ℝ)
  set f : H E n 0 → ℂ := fun x => ψ₁.1 x.1 * u (-ldet x) with hf
  have hmem : MemLp f 2 s.D.ν := (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n s.pos s.D s.π s.fix ψ₁ hψ₁ _ hw hws).1
  set v : Lp ℂ 2 s.D.ν := hmem.toLp f with hvdef
  have hv : (v : H E n 0 → ℂ) =ᵐ[s.D.ν] f := hmem.coeFn_toLp
  have hP : P0 s.D s.π v = v := cusp_projection_self s.D s.π hψ₁ hw hws v hv
  obtain ⟨kI, kE⟩ := hKer E n ι s m v x₀
  rw [hP] at kE
  have hψinv : ∀ (γ : ratH E n 0) (y : H E n 0), ψ₁.1 ((γ : H E n 0) * y).1 = ψ₁.1 y.1 := by
    intro γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    rw [Prod.fst_mul, h1]
    exact (s.π.cusp ψ₁ hψ₁).1.left γ₁ y.1
  have hfinv : ∀ (γ : ratH E n 0) (y : H E n 0), f ((γ : H E n 0) * y) = f y := by
    intro γ y
    simp only [hf]
    rw [hψinv γ y, bMul, (bRat γ).1, zero_add]
  have hGinv : ∀ (γ : ratH E n 0) (y : H E n 0), m.G x₀ (th ((γ : H E n 0) * y)) = m.G x₀ (th y) := by
    intro γ y
    have h2 := hK E n ι s |>.2 ⟨th (γ : H E n 0), (bRat γ).2⟩ (th y)
    simp only [Mid.G, Gk]
    rw [bThMul, h2]
  set F : H E n 0 → ℂ := fun y => f y * m.G x₀ (th y) with hF
  have hFinv : Inv F := fun γ y => by
    simp only [hF]
    rw [hfinv, hGinv]
  have hFint : Integrable F s.D.ν := kI.congr (hv.mono fun y hy => by simp only [hF, hy])
  obtain ⟨tI, tE⟩ := hTI E n s.D F hFinv hFint
  have hFth : ∀ x, F (th x) = ψ.1 x.1 * m.G x₀ x * u (ldet x) := by
    intro x
    have h1 : ψ₁.1 (th x).1 = ψ.1 x.1 := by
      have e : thetaA E n (th x).1 = x.1 := congrArg Prod.fst (bThTh x)
      rw [hψe, e]
    simp only [hF, hf]
    rw [h1, bThL, neg_neg, bThTh]
    ring
  refine ⟨tI.congr (Filter.Eventually.of_forall hFth), ?_⟩
  have hμl : s.D.μ.IsMulLeftInvariant := s.D.haar.1
  haveI hmm : MeasurableMul (H E n 0) :=
    (inferInstance : MeasurableMul (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds s.D).G)
  have hun := (DiscreteGroups.T1.G.unfold (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds s.D)
    PositivityTheory.Rg.BcB.E1.kerBasic PositivityTheory.Rg.BcB.E1.kernel_rows_columns_square_integrable (tst_trM s.D m.t s.M) (f := f) hfinv hmem x₀).2
  have hun' : ∫ y, kerH m.φ x₀ y * f y ∂s.D.ν = ∫ y, m.φ (x₀⁻¹ * y) * f y ∂s.D.μ := hun
  calc ∫ x, ψ.1 x.1 * m.G x₀ x * u (ldet x) ∂s.D.ν
      = ∫ x, F (th x) ∂s.D.ν := integral_congr_ae (Filter.Eventually.of_forall fun x => (hFth x).symm)
    _ = ∫ x, F x ∂s.D.ν := tE
    _ = ∫ y, (v : H E n 0 → ℂ) y * m.G x₀ (th y) ∂s.D.ν :=
        integral_congr_ae (hv.mono fun y hy => by simp only [hF, hy])
    _ = ∫ y, kerH m.φ x₀ y * (v : H E n 0 → ℂ) y ∂s.D.ν := kE
    _ = ∫ y, kerH m.φ x₀ y * f y ∂s.D.ν := integral_congr_ae (hv.mono fun y hy => by simp only [hy])
    _ = ∫ y, m.φ (x₀⁻¹ * y) * f y ∂s.D.μ := hun'
    _ = ∫ z, m.φ (x₀⁻¹ * (x₀ * z)) * f (x₀ * z) ∂s.D.μ :=
        (integral_mul_left_eq_self (fun y => m.φ (x₀⁻¹ * y) * f y) x₀).symm
    _ = ∫ z, m.φ z * ψ.1 (thetaA E n (x₀.1 * z.1)) * u (-(ldet x₀ + ldet z)) ∂s.D.μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [hf]
        rw [inv_mul_cancel_left, bMul, Prod.fst_mul, hψe]
        ring

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SuppPf
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.supp_pf :
    Basic → Zero → KInv → PSupp → Ker → Supp := by
  intro hB hZ hK hP hKer E _ _ _ n ι _ s m R hR x y hxy
  obtain ⟨hac, hmul, -, -, hone, -, hldth, hthth, hthmul, hrat, -, hthc⟩ := hB E n s.pos
  have hl1 : ldet (1 : H E n 0) = 0 := by
    have h := hac 0
    rwa [hone] at h
  have hlinv : ∀ z : H E n 0, ldet z⁻¹ = -ldet z := by
    intro z
    have h := hmul z z⁻¹
    rw [mul_inv_cancel, hl1] at h
    linarith
  have hf : Continuous fun w : H E n 0 => m.G x (th w) := by
    show Continuous fun w : H E n 0 => ∑ i, inner ℂ (s.k₁ x i) (m.Uπ (s.k₂ (th w) i))
    refine continuous_finsetSum _ fun i _ => ?_
    exact continuous_const.inner (m.Uπ.continuous.comp (((s.vecs.cont i).2).comp hthc))
  have hinv : Inv fun w : H E n 0 => m.G x (th w) := by
    intro γ w
    have h := (hK E n ι s).2 ⟨th (γ : H E n 0), (hrat γ).2⟩ (th w)
    show Gk s.k₁ s.k₂ m.Uπ x (th ((γ : H E n 0) * w)) = Gk s.k₁ s.k₂ m.Uπ x (th w)
    rw [hthmul]
    unfold Gk
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show s.k₂ (th (γ : H E n 0) * th w) = s.k₂ (th w) from h]
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = (|ldet x + ldet y| - R) / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have key := hZ E n s.D (fun w => m.G x (th w)) (Set.Ioo (-ldet y - δ) (-ldet y + δ)) hf hinv isOpen_Ioo ?_ (th y) ?_
  · simpa only [hthth] using key
  · intro v hv
    refine ((hKer E n ι s m v x).2).trans ?_
    have hPv := hP E n s.D s.π (-ldet y - δ) (-ldet y + δ) v
      (hv.mono fun w h h' => h fun hI => h' (Set.Ioo_subset_Icc_self hI))
    apply integral_eq_zero_of_ae
    filter_upwards [hPv] with w hw
    by_cases hI : ldet w ∈ Set.Icc (-ldet y - δ) (-ldet y + δ)
    · have hk : kerH m.φ x w = 0 := by
        unfold kerH
        refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
        by_contra hne
        have h1 := hR _ hne
        rw [hmul, hmul, hlinv, (hrat γ).1] at h1
        obtain ⟨a1, a2⟩ := abs_le.mp h1
        obtain ⟨b1, b2⟩ := hI
        rcases abs_cases (ldet x + ldet y) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hδ <;> linarith
      simp [hk]
    · simp [hw hI]
  · rw [hldth]
    exact ⟨by linarith, by linarith⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.WeakPf
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem ctx_fub (X : Ctx) (φ : X.G → ℂ) (hφ : Tst φ) (g f : X.G → ℂ) (hg : MemLp g 2 X.ν) (hf : MemLp f 2 X.ν) :
    Integrable (fun y => (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y) X.ν ∧
      Integrable (fun z => g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν) X.ν ∧
      ∫ y, (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y ∂X.ν = ∫ z, g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν ∂X.ν := by
  obtain ⟨A, hA, h1, h2⟩ := rowInt X φ hφ
  have hm : Measurable (Function.uncurry (ker X.Γ φ)) := (kerBasic X φ hφ).2.1.measurable
  have hν : SFinite X.ν := by unfold Ctx.ν; infer_instance
  have hP := schurInt X.G X.ν (ker X.Γ φ) A hm hA h1 h2 g f hg hf
  have e1 : ∀ y, ∫ z, g z * ker X.Γ φ z y * f y ∂X.ν = (∫ z, g z * ker X.Γ φ z y ∂X.ν) * f y :=
    fun y => integral_mul_const _ _
  have e2 : ∀ z, ∫ y, g z * ker X.Γ φ z y * f y ∂X.ν = g z * ∫ y, ker X.Γ φ z y * f y ∂X.ν := fun z => by
    simp_rw [mul_assoc]; exact integral_const_mul _ _
  refine ⟨?_, ?_, ?_⟩
  · simpa only [e1] using hP.integral_prod_right
  · simpa only [e2] using hP.integral_prod_left
  · simp_rw [← e1, ← e2]
    exact (integral_integral_swap (f := fun z y => g z * ker X.Γ φ z y * f y) hP).symm

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.weak_pf :
    Weak := by
  intro E _ _ _ n ι _ s v u i
  have hth : ∀ y : H E n 0, th (th y) = y := fun y =>
    Prod.ext (GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol _) (GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol _)
  let c : ι → ℂ := fun l => s.M l i
  let g : ι → H E n 0 → ℂ := fun j z => starRingEnd ℂ ((u j : H E n 0 → ℂ) z)
  have hg : ∀ j, MemLp (g j) 2 s.D.ν := fun j => (Lp.memLp (u j)).star
  have F : ∀ j l, Integrable (fun y => (∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y) s.D.ν ∧
      Integrable (fun z => g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν) s.D.ν ∧
      ∫ y, (∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y ∂s.D.ν =
        ∫ z, g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν ∂s.D.ν := fun j l =>
    ctx_fub (ctx ratProper_holds s.D) (s.Φ₂ j l) (s.t₂ j l) (g j) v (hg j) (Lp.memLp v)
  have hrep : ∀ y, (v : H E n 0 → ℂ) y * inner ℂ u (s.k₂ (th y) i) =
      ∑ j, ∑ l, c l * ((∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y) := by
    intro y
    rw [s.vecs.rep₂ (th y) i u, hth, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const]
    ring
  have hv : ∀ (l : ι) (φ : H E n 0 → ℂ), ∫ y, φ y * ((vecM v c l : Lp ℂ 2 s.D.ν) : H E n 0 → ℂ) y ∂s.D.ν =
      c l * ∫ y, φ y * (v : H E n 0 → ℂ) y ∂s.D.ν := by
    intro l φ
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    have e : (vecM v c l : Lp ℂ 2 s.D.ν) = c l • v := rfl
    filter_upwards [Lp.coeFn_smul (c l) v] with y hy
    rw [e, hy, Pi.smul_apply, smul_eq_mul]
    ring
  have hR : inner ℂ u (s.T₂ (vecM v c)) =
      ∑ j, ∑ l, c l * ∫ z, g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν ∂s.D.ν := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [L2.inner_def]
    have h : (fun z => inner ℂ ((u j : Lp ℂ 2 s.D.ν) z) ((s.T₂ (vecM v c) j : Lp ℂ 2 s.D.ν) z)) =ᵐ[s.D.ν]
        fun z => ∑ l, c l * (g j z * ∫ y, kerH (s.Φ₂ j l) z y * (v : H E n 0 → ℂ) y ∂s.D.ν) := by
      filter_upwards [s.o₂ (vecM v c) j] with z hz
      rw [hz, RCLike.inner_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hv]
      simp only [g]
      ring
    rw [integral_congr_ae h, integral_finsetSum _ fun l _ => (F j l).2.1.const_mul _]
    exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
  have hint : Integrable (fun y => ∑ j, ∑ l, c l *
      ((∫ z, g j z * kerH (s.Φ₂ j l) z y ∂s.D.ν) * (v : H E n 0 → ℂ) y)) s.D.ν :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => (F j l).1.const_mul _
  refine ⟨?_, ?_⟩
  · simpa only [hrep] using hint
  · simp only [hrep]
    change _ = inner ℂ u (s.T₂ (vecM v c))
    rw [hR, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => (F j l).1.const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => (F j l).1.const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, (F j l).2.2]

end
end

