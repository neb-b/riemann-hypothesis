module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0096
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0050
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0038
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SecUnfOfCLaw
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0053
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0095
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0066
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0074
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0013
public import Development.AutomorphicArithmetic.AdelicQuotients.UnitaryLocalGroupLeOffPlacesEmpty
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0073
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0064

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.MainLawK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.SiegelLawDblTargetF
theorem lagr_law_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (χS (Matrix.GeneralLinearGroup.det t) : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd
  obtain ⟨α, hαc, hαr, hlaw⟩ := _root_.GlobalTheory.T.fundamental_domain_haar_plancherel F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd
  intro h t hht f hf
  by_cases h0 : ∀ g, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ g →
      GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) g = 0
  · rw [h0 _ (hωd.om_pres _ f hf), h0 f hf, mul_zero]
  push_neg at h0
  obtain ⟨f₀, hf₀, hne⟩ := h0
  have hsp := _root_.GlobalTheory.T.fundamental_domain_haar_parseval F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd α hlaw f₀ hf₀ hne
  have hα : ∀ a : GL (Fin nT) (AF F ⊗[F] E), α a = χS (Matrix.GeneralLinearGroup.det a) := by
    rcases Nat.eq_zero_or_pos nT with hn0 | hpos
    · intro a
      have hd : Matrix.GeneralLinearGroup.det a = 1 := by
        ext; rw [Matrix.GeneralLinearGroup.val_det_apply]; subst hn0; simp
      rw [char_det_one F E nT α a hd, hd, map_one]
    obtain ⟨i0⟩ : Nonempty (Fin nT) := ⟨⟨0, hpos⟩⟩
    have hhec : IsHeckeCharF (α.comp (GlobalTheory.LeviOrigin.dgU nT i0) * χS⁻¹) := by
      refine ⟨?_, ?_⟩
      · exact (hαc.comp (GlobalTheory.LeviOrigin.continuous_dgU nT i0)).mul (hωd.hecS.1.inv)
      · intro x
        rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, hωd.hecS.2 x, inv_one, mul_one,
          GlobalTheory.LeviOrigin.dgU_map (incAF F E) nT i0 x]
        exact hαr _
    have hν1 := _root_.GlobalTheory.T.hecke_character_trivial_of_split F E σ B hB _ hhec (by
      intro e he x hx
      have h2 := hsp e he (GlobalTheory.LeviOrigin.dgU nT i0 x) (by
        intro k l
        rw [GlobalTheory.LeviOrigin.dgU_sub_one]
        split_ifs
        · exact hx
        · exact mul_zero _)
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, h2, GlobalTheory.LeviOrigin.det_dgU, MonoidHom.inv_apply,
        mul_inv_cancel])
    have hdg : ∀ x, α (GlobalTheory.LeviOrigin.dgU nT i0 x) = χS x := by
      intro x
      have := hν1 x
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply] at this
      exact mul_inv_eq_one.mp this
    intro a
    have hb : Matrix.GeneralLinearGroup.det (a * (GlobalTheory.LeviOrigin.dgU nT i0 (Matrix.GeneralLinearGroup.det a))⁻¹) = 1 := by
      rw [map_mul, map_inv, GlobalTheory.LeviOrigin.det_dgU, mul_inv_cancel]
    have h3 : α a = α (a * (GlobalTheory.LeviOrigin.dgU nT i0 (Matrix.GeneralLinearGroup.det a))⁻¹) *
        α (GlobalTheory.LeviOrigin.dgU nT i0 (Matrix.GeneralLinearGroup.det a)) := by
      rw [← map_mul, inv_mul_cancel_right]
    rw [h3, char_det_one F E nT α _ hb, one_mul]
    exact hdg _
  rw [hlaw h t hht f hf, hα t]
theorem main_law_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.ResEtaF χS nS →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
          Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
            Module.End ℂ ((κ → AF F) → ℂ),
          GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ωd omp →
      ∀ (p : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)) (t : GL (Fin nT) (AF F ⊗[F] E)),
        p.1.1 * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
      ∀ Φ ∈ schA F κ, omp (p, 1) Φ ∈ schA F κ ∧
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (omp (p, 1) Φ)) =
          (χS (Matrix.GeneralLinearGroup.det t) : ℂ) *
            ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
              (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) *
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ JB ξ hξ κ _ co hco ν 𝓕 hν h𝓕 χS hχS rχS ωd hωd omp htr p t hpt Φ hΦ
  obtain ⟨h, hh⟩ := exists_gaf σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) p
  have hg : mtF σ JS 1 = ((1 : UG (cA σ) (incM F JB))⁻¹).1.1ᵀ := by
    first
      | (simp only [mtF, map_one, inv_one]; simp; done)
      | (simp [mtF, matHomF]; exact map_one _)
      | (simp [mtF, matHomF]; rfl)
  obtain ⟨hmem, heq⟩ := htr p 1 1 h hh hg Φ hΦ
  refine ⟨hmem, ?_⟩
  erw [heq]
  have hth := _root_.GlobalTheory.TransportHeisF.isThetaFunOF_thetaTr_k F E σ B hB nS (nT + nT) JS
    (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hS (GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT) ξ₀ hξ₀ hσ hωd.std _ JB ξ
    rfl hξ κ co hco Φ hΦ
  exact _root_.GlobalTheory.SiegelLawDblTargetF.lagr_law_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd h t (by rw [hh]; exact hpt) _ hth
end GlobalTheory.SiegelLawDblTargetF
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SecUnfOfCLawK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act
theorem secUnf_of_cLaw_k : _root_.PositivityTheory.SiegelWeilFormula.Act.AbsConv_k → _root_.PositivityTheory.SiegelWeilFormula.Act.CLawEx_k → _root_.PositivityTheory.SiegelWeilFormula.Act.SecUnf_k := by
  intro hA hL F E _ _ _ _ _ σ d R L s₁ f hf he
  obtain ⟨t, ht⟩ := hA F E σ d L s₁ f hf he
  refine ⟨t, fun z hz nb lam 𝓖 hc hk uM ν 𝓤 hU hkU T T' hT nb' lam' 𝓖' hc' hk' => ?_⟩
  obtain ⟨w₁, cM, κ, hlaw, hw, hwf, hcM, hκ, δ, hδ, hcf⟩ := hL F E σ d R L
  have h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ :=
    { nb := hc.1, uM := hU.1, nb' := hc'.1, wr := hw, wf := hwf, cf := hcf, δ0 := hδ }
  obtain ⟨K, hK⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.unf_k R hf z hc hU hT hc' (fun x => ht z hz nb lam 𝓖 hc hk uM ν 𝓤 hU hkU T x) h hcM hκ
  exact ⟨w₁, cM, κ, hlaw, K, fun x => hK x⟩
theorem secUnf_of_k : _root_.PositivityTheory.SiegelWeilFormula.Act.AbsConv_k → _root_.PositivityTheory.SiegelWeilFormula.Act.SecUnf_k := fun hA => _root_.PositivityTheory.SiegelWeilFormula.Act.secUnf_of_cLaw_k hA _root_.PositivityTheory.SiegelWeilFormula.Act.cLawEx_k
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldModel
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem modelEx_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k := _root_.PositivityTheory.SiegelWeilFormula.Ald.modelExists_of_siegelSmall (_root_.PositivityTheory.SiegelWeilFormula.Ald.siegelSmall_of_slice_k sliceFacts)
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGNonVan
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TP
private theorem nv_sf_pk {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : SFinite μ := inferInstance
end UpperTheory.TP
open UpperTheory.TP
set_option maxHeartbeats 2000000 in
theorem _root_.UpperTheory.TP.nonVan_k :
    _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.Rallis_k → _root_.UpperTheory.TP.Decomp_k → _root_.UpperTheory.TP.BumpAny_k → _root_.UpperTheory.TP.Datum_k → _root_.UpperTheory.TP.Tail_k → UpperTheory.TP.AbsNe → _root_.UpperTheory.TP.SchurStep_k → _root_.UpperTheory.TP.NonVan_k := by
  intro T hR hD hBu hDa hTl hAb hSc E _ _ _ B n d X W M χX χW om hP hn e e' he he' hd K a ε hK ha hε t₀ ht hlt U hU f₀ hf₀ hf0 φ hφ0 hS
  classical
  obtain ⟨a1, a2, a3⟩ := Euler.lcsc_UA (cj E) X.J
  have hC : Cpt (cj E) X.J := T.cpt _ E (cj E) B n X n 0 hP.base (Or.inl hP.herm) (by simp)
  have hS' := hS
  have hA : GlobalTheory.UnitaryBC.IsAutFormU φ := by
    obtain ⟨V, _, _, _, ρ, i, jj, x₀, -, -, hjx, hjU, -, -⟩ := hS'
    exact hU.aut φ (hjx ▸ hjU x₀)
  set φ' : UA (cj E) X.J → ℂ := φ ∘ e.symm with hφ'
  have hfn : IsFn φ' := ⟨hA.cont.comp e.symm.continuous, fun γ hγ g => by
    have h1 : e.symm γ ∈ GlobalTheory.UnitaryBC.ratU E n := (he.rat _).1 (by simpa using hγ)
    simpa [hφ'] using hA.left _ h1 (e.symm g)⟩
  have hφ'0 : φ' ≠ 0 := fun h => hφ0 (funext fun g => by simpa [hφ'] using congrFun h (e g))
  obtain ⟨r, r0, r1, r2⟩ := UpperTheory.matrix_coefficient_bounded_by_value_at_one (M := M) hC hP.good.haar hP.good.dom hfn hφ'0
  obtain ⟨O, oO, eO⟩ := isOpen_induced_iff.1 hA.level
  have one_O : (1 : GlobalTheory.UnitaryBC.UA E n) ∈ O := by
    have : (1 : GlobalTheory.UnitaryBC.finU (E := E) (n := n)) ∈ Subtype.val ⁻¹' O := by
      rw [eO]; show GlobalTheory.UnitaryBC.RU E n 1 φ = φ; rw [map_one]; rfl
    exact this
  set N : Set (UA (cj E) X.J) := e.symm ⁻¹' O with hN
  have oN : IsOpen N := oO.preimage e.symm.continuous
  have one_N : (1 : UA (cj E) X.J) ∈ N := by simpa [hN] using one_O
  have hfix : ∀ g ∈ gOff (cj E) X ∅, g ∈ N → ∀ y, φ' (y * g) = φ' y := fun g hg hgN y => by
    have k1 : e.symm g ∈ GlobalTheory.UnitaryBC.finU (E := E) (n := n) := (he.fin _).1 (by simpa using hg)
    have k2 : (⟨e.symm g, k1⟩ : GlobalTheory.UnitaryBC.finU (E := E) (n := n)) ∈ {k : GlobalTheory.UnitaryBC.finU (E := E) (n := n) | GlobalTheory.UnitaryBC.RU E n k φ = φ} := by
      rw [← eO]; exact hgN
    have : φ (e.symm y * e.symm g) = φ (e.symm y) := congrFun k2 (e.symm y)
    simpa [hφ'] using this
  obtain ⟨⟨j0, hj0⟩, -, -, -, cK0, -, -, -, -⟩ := hD _ E (cj E) B n X hP.base hP.herm ∅
  have clOff : ∀ S, IsClosed (gOff (cj E) X S : Set (UA (cj E) X.J)) := fun S =>
    (hD _ E (cj E) B n X hP.base hP.herm S).2.2.2.1
  obtain ⟨S₀, hS₀⟩ := _root_.UpperTheory.exists_finite_places_integral_mem_nhds_one hP.base hP.herm cK0 clOff (oN.mem_nhds one_N)
  obtain ⟨R, hRam⟩ := _root_.UpperTheory.exists_finite_unramified_outside_of_isHecke hP.base hP.hW
  have hint := ht _ hlt.le
  obtain ⟨S, hSS, hTail⟩ := hTl _ E (cj E) B n X hP.base hP.herm K a ε hK ha hε M.μ ((d : ℝ) / 2) hP.good.haar hint (S₀ ∪ R)
  have hOffS : gOff (cj E) X S ≤ gOff (cj E) X S₀ := Subgroup.closure_mono fun g hg =>
    ⟨hg.1, fun v hv => hg.2 v (hSS (Finset.mem_union_left _ hv))⟩
  have hOff0 : gOff (cj E) X S ≤ gOff (cj E) X ∅ := Subgroup.closure_mono fun g hg =>
    ⟨hg.1, fun v hv => absurd hv (by simp)⟩
  have hunr : UnrOff χW (S : Set (Pl (maximalRealSubfield E))) := fun w hw => hRam w fun h => hw (by
    simp only [above, Set.mem_setOf_eq] at h ⊢
    exact hSS (Finset.mem_union_right _ h))
  have hbump := fun v => hBu _ E (cj E) B n d X W M χX χW om hP hn hd v N (oN.mem_nhds one_N)
  choose H b hb hHN using hbump
  set φf : ∀ v : Pl (maximalRealSubfield E), (Fin n × Fin d → Fv (maximalRealSubfield E) v) → ℂ :=
    fun v => if v ∈ S then b v else M.vac v with hφf
  have hfin : IsFin M φf := by
    refine ⟨fun v => ?_, ?_⟩
    · by_cases hv : v ∈ S
      · simpa [hφf, hv] using (hb v).1
      · simpa [hφf, hv] using (hP.good.vac v).1
    · filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hv
      simp [hφf, hv]
  letI : MeasurableSpace (Fin n × Fin d → AF (maximalRealSubfield E)) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF (maximalRealSubfield E)) := ⟨rfl⟩
  let ν : Measure (Fin n × Fin d → AF (maximalRealSubfield E)) := Measure.addHaar
  have hν : ν.IsAddHaarMeasure := inferInstance
  obtain ⟨hc1, hco⟩ := hDa _ E (cj E) B n d X W M χX χW om hP hn K a ε hK ha hε ν hν S hunr H φf hfin
    (fun v hv => by simpa [hφf, hv] using hb v) (fun v hv => by simp [hφf, hv]) f₀ hf₀ hf0
  obtain ⟨⟨j, hj⟩, cInf, clAt, clOff', cK, oK, -, hcomp, -⟩ := hD _ E (cj E) B n X hP.base hP.herm S
  let Tst : Subgroup (UA (cj E) X.J) :=
    { carrier := {g | ∀ y, φ' (y * g) = φ' y}
      one_mem' := fun y => by rw [mul_one]
      mul_mem' := fun {g h} hg hh y => by rw [← mul_assoc, hh, hg]
      inv_mem' := fun {g} hg y => by rw [← hg (y * g⁻¹), inv_mul_cancel_right] }
  have hHfix : (⨆ v ∈ S, H v) ≤ Tst := iSup₂_le fun v _ g hg =>
    hfix g (UpperTheory.unitaryLocalGroup_le_offPlaces_empty v ((hb v).2.2.1 hg)) (hHN v hg)
  have hcomm : ∀ (b : gAt (cj E) X S) (c : gOff (cj E) X S), b.1 * c.1 = c.1 * b.1 := fun b c => by
    have h1 : j ((1, (b, 1)) * (1, (1, c))) = j ((1, (1, c)) * (1, (b, 1))) := by
      congr 1
      simp
    rw [map_mul, map_mul, hj, hj] at h1
    simpa using h1
  have hmc : ∀ (x : UA (cj E) X.J) (b : gAt (cj E) X S) (c : gOff (cj E) X S), b.1 ∈ (⨆ v ∈ S, H v) →
      mc M φ' (x * b.1 * c.1) = mc M φ' (x * c.1) := fun x b c hbH => by
    have : (fun y => φ' (y * (x * b.1 * c.1))) = fun y => φ' (y * (x * c.1)) := funext fun y => by
      rw [mul_assoc x, hcomm, ← mul_assoc x, ← mul_assoc y]
      exact hHfix hbH _
    simp only [mc, this]
  haveI : LocallyCompactSpace (gInf (cj E) X) := cInf.isClosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (gAt (cj E) X S) := clAt.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (gOff (cj E) X S) := clOff'.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μA : Measure (gInf (cj E) X) := Measure.haar
  let μB : Measure (gAt (cj E) X S) := Measure.haar
  let μC : Measure (gOff (cj E) X S) := Measure.haar
  haveI : SFinite μA := nv_sf_pk μA
  haveI : SFinite μB := nv_sf_pk μB
  haveI : SFinite μC := nv_sf_pk μC
  obtain ⟨κ, hκ, hκe⟩ := hSc E B n d X W M χX χW om hP hn e e' he he' U hU f₀ hf0 φ hφ0 hS ν hν φf hfin μA inferInstance
  have hPol : pure f₀ φf ∈ PolData B M := Submodule.subset_span ⟨f₀, hf₀, φf, hfin.1, hfin.2, rfl⟩
  obtain ⟨hI, hZ⟩ := hR _ E (cj E) B n d X W M χX χW om hP hn (by omega) K a ε hK ha hε t₀ ht hlt ν hν _ hPol φ' hfn
  refine ⟨φf, hfin, fun h0 => ?_⟩
  obtain ⟨hIP, c, hc⟩ := UpperTheory.haarMeasure_triple_product_decomposition _ _ _ cInf.isClosed clAt clOff' j M.μ hP.good.haar μA μB μC inferInstance inferInstance
    inferInstance _ hI
  rw [hZ h0, mul_zero] at hc
  choose s s1 s2 s3 using fun c : gOff (cj E) X S => (hco 1 (one_mem _) 1 (one_mem _) c.1 c.2).2
  have oH := UpperTheory.unitaryAdelic_mem_of_localGroups_near_one S H (fun v _ => (hb v).2.2.2.2.1) hcomp
  have hIG : ∀ g ∈ (⨆ v ∈ S, H v), IntAll g := fun g hg =>
    Subgroup.mem_iInf.1 ((iSup₂_le fun v _ g hg => Subgroup.mem_iInf.2 fun w =>
      Bad.int_all ((hb v).2.2.1 hg) ((hb v).2.2.2.1 g hg) w : (⨆ v ∈ S, H v) ≤ ⨅ w, Euler.intGrp (cj E) X w) hg)
  have cB : IsCompact {b : gAt (cj E) X S | IntAll b.1} := clAt.isClosedEmbedding_subtypeVal.isCompact_preimage cK
  have cC : IsCompact {c : gOff (cj E) X S | IntAll c.1} := clOff'.isClosedEmbedding_subtypeVal.isCompact_preimage cK
  refine hAb _ _ _ μA μB μC {b | b.1 ∈ ⨆ v ∈ S, H v} {c | IntAll c.1} oH.measurableSet
    (oK.preimage continuous_subtype_val).measurableSet (oH.measure_ne_zero μB ⟨1, one_mem (⨆ v ∈ S, H v)⟩)
    (ne_top_of_le_ne_top cB.measure_lt_top.ne (measure_mono fun b hb' => hIG _ hb')) cC.measure_lt_top.ne
    _ (fun x c => coef om ν (pure f₀ φf) x.1 * star (mc M φ' (x.1 * c.1))) s (fun c => star (mc M φ' c.1))
    (κ * coef om ν (pure f₀ φf) 1) r (fun c => ENNReal.ofReal (a (ε (c.1, 1)) ^ ((d : ℝ) / 2)))
    (mul_ne_zero hκ hc1) r0 hIP ?_ ?_ ?_ ?_ ?_ (hTail μC inferInstance) hc
  · intro x b c hb'
    rw [hj]
    rw [(hco x.1 x.2 b.1 b.2 c.1 c.2).1 hb', zero_mul]
  · intro x c b hb'
    rw [hj]
    simp only
    rw [s3 c x.1 x.2 b.1 hb', hmc _ _ _ hb', mul_assoc]
  · intro c
    exact hκe c.1 (hOff0 c.2)
  · intro c hc'
    refine ⟨s2 c hc', ?_⟩
    have : (fun y => φ' (y * c.1)) = fun y => φ' (y * 1) := funext fun y => by
      rw [mul_one]; exact hfix _ (hOff0 c.2) (hS₀ _ (hOffS c.2) hc') y
    have e1 : mc M φ' c.1 = r := by rw [← r1]; simp only [mc, this]
    simp [e1]
  · intro c
    refine ⟨by simpa using r2 c.1, ?_⟩
    rw [← s1 c, ofReal_norm_eq_enorm]
end
end
end

