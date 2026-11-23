module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedInductionProductParabolicPiTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0778
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0005
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleOfBaseChangeField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefFieldDescent

theorem interNum_one_nonneg_of_isNef {k : Type} [Field k] {V : Scheme.{0}} [Algebra k Γ(V, ⊤)]
    (hp : IsProjOver (strHom k (X := V))) (hd : topologicalKrullDim V ≤ 1) {N : LB V} (hN : IsNef k N) :
    0 ≤ interNum k (GlobalTheory.structureModule V) ![N] := by
  refine CurveDevissage.interNum_one_nonneg hp hd hN.isLB (fun Z i hi hZ _ ha hdZ => ?_) _ inferInstance
  have hpr : IsProper (strHom k (X := V)) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  have h := (isNef_iff_isClosedImmersion.1 hN).2 Z i hi hZ hdZ inferInstance
  rw [interNumOn, interNum_pushforward_of_isClosedImmersion ha _ (isLB_vecOne hN.isLB)] at h
  rw [topSelf_def]
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j; rfl

theorem isNef_of_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ L : LB Y, L.IsLB → (letI := algebraΓOfHom q; IsNef E (L.pull π)) → (letI := algebraΓOfHom p; IsNef k L) := by
  intro k E _ _ _ Y X p q π H hp L hL hN
  letI := algebraΓOfHom p
  letI := algebraΓOfHom q
  refine ⟨hL, fun C hC => ?_⟩
  have H₁ : IsPullback (pullback.fst (redι C) π) (pullback.snd (redι C) π ≫ q) (redι C ≫ p)
      (spMap (algebraMap k E)) := (IsPullback.of_hasPullback (redι C) π).paste_vert H
  have hpC : IsProjOver (redι C ≫ p) := ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
  have hpr : IsProper (redι C ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hpC).1
  have hp' := ProjSpace.isProjOver_of_isPullback_spMap _ H₁ hpC
  have hd : topologicalKrullDim (pullback (redι C) π : Scheme.{0}) ≤ 1 :=
    (FieldExtDim.topologicalKrullDim_baseChange_le k E _ _ _ _ _ H₁).trans
      ((topologicalKrullDim_red C).trans hC.2).le
  have hLC := LB.isLB_pull hL (redι C)
  have key := FieldChangeInter.interNum_pull H₁ (isLB_vecOne hLC)
  letI := algebraΓOfHom (pullback.snd (redι C) π ≫ q)
  have hN' : IsNef E ((L.pull π).pull (pullback.snd (redι C) π)) :=
    hN.pull_of_isClosedImmersion _ fun _ => rfl
  have h0 := interNum_one_nonneg_of_isNef (k := E)
    (by rw [strHom_eq (f := pullback.snd (redι C) π ≫ q) fun _ => rfl]; exact hp') hd hN'
  rw [interNumRed_one_eq hL]
  refine (h0.trans_eq ?_).trans_eq key
  refine interNum_congr_cls E _ (isLB_vecOne hN'.isLB)
    (fun i => LB.isLB_pull (isLB_vecOne hLC i) _) fun i => ?_
  fin_cases i
  change pull _ (pull π (cls L hL)) = pull _ (pull (redι C) (cls L hL))
  simp only [← pull_comp, pullback.condition]

end GlobalTheory.NefFieldDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackGluedQuotientKernelPairOfCover
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GlueQuotPB

theorem isIso_of_isPullback_openCover {X Y : Scheme.{0}} (f : X ⟶ Y) (𝒱 : Y.OpenCover)
    {Z : 𝒱.I₀ → Scheme.{0}} (k : ∀ i, Z i ⟶ X) (g : ∀ i, Z i ⟶ 𝒱.X i)
    (h : ∀ i, IsPullback (k i) (g i) f (𝒱.f i)) (hg : ∀ i, IsIso (g i)) : IsIso f := by
  have key := (IsZariskiLocalAtTarget.iff_of_openCover (P := MorphismProperty.isomorphisms Scheme.{0})
    (f := f) 𝒱).2
  refine key fun i => ?_
  have e : ((h i).isoIsPullback _ _ (IsPullback.of_hasPullback f (𝒱.f i))).hom ≫
      pullback.snd f (𝒱.f i) = g i := by simp
  change IsIso (pullback.snd f (𝒱.f i))
  have hgi := hg i
  have e2 : pullback.snd f (𝒱.f i) =
      ((h i).isoIsPullback _ _ (IsPullback.of_hasPullback f (𝒱.f i))).inv ≫ g i := by
    exact (Iso.eq_inv_comp _).2 e
  rw [e2]
  infer_instance

theorem isIso_of_pullback_openCover {S : Scheme.{0}} (𝒰 : S.OpenCover) {X Y : Over S} (c : X ⟶ Y)
    (hc : ∀ j, IsIso ((Over.pullback (𝒰.f j)).map c)) : IsIso c := by
  suffices hl : IsIso c.left by
    have : IsIso ((Over.forget S).map c) := hl
    exact isIso_of_reflects_iso c (Over.forget S)
  refine isIso_of_isPullback_openCover c.left (𝒰.pullback₁ Y.hom)
    (fun j => pullback.fst X.hom (𝒰.f j)) (fun j => ((Over.pullback (𝒰.f j)).map c).left) (fun j => ?_)
    (fun j => by
      have := hc j
      exact (inferInstance : IsIso ((Over.forget _).map ((Over.pullback (𝒰.f j)).map c))))
  refine IsPullback.of_bot (v₂₁ := pullback.snd Y.hom (𝒰.f j)) (v₂₂ := Y.hom) (h₃₁ := 𝒰.f j) ?_ ?_
    (IsPullback.of_hasPullback Y.hom (𝒰.f j))
  · convert IsPullback.of_hasPullback X.hom (𝒰.f j) using 1
    · simp only [Over.pullback_map_left]
      erw [pullback.lift_snd]
    · exact Over.w c
  · change _ = _ ≫ pullback.fst Y.hom (𝒰.f j)
    simp only [Over.pullback_map_left]
    erw [pullback.lift_fst]

theorem hom_ext_of_pullback_openCover {S : Scheme.{0}} (𝒰 : S.OpenCover) {X Y : Over S} (f g : X ⟶ Y)
    (h : ∀ j, (Over.pullback (𝒰.f j)).map f = (Over.pullback (𝒰.f j)).map g) : f = g := by
  ext1
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ X.hom) _ _ fun j => ?_
  have e := congrArg (fun u => u.left ≫ pullback.fst Y.hom (𝒰.f j)) (h j)
  change pullback.fst X.hom (𝒰.f j) ≫ f.left = pullback.fst X.hom (𝒰.f j) ≫ g.left
  simp only [Over.pullback_map_left] at e
  erw [pullback.lift_fst, pullback.lift_fst] at e
  exact e

theorem baseChange_translation {T T' : Scheme.{0}} (t : T' ⟶ T) (A H : Over T) [GrpObj A] [GrpObj H] (i : H ⟶ A) :
    ∃ e : (Over.pullback t).obj (H ⊗ A) ≅ (Over.pullback t).obj H ⊗ (Over.pullback t).obj A,
      e.hom ≫ ((fst ((Over.pullback t).obj H) ((Over.pullback t).obj A) ≫ (Over.pullback t).map i) *
          snd ((Over.pullback t).obj H) ((Over.pullback t).obj A)) =
        (Over.pullback t).map ((fst H A ≫ i) * snd H A) ∧
      e.hom ≫ snd ((Over.pullback t).obj H) ((Over.pullback t).obj A) = (Over.pullback t).map (snd H A) := by
  refine ⟨(Functor.Monoidal.μIso (Over.pullback t) H A).symm, ?_, ?_⟩
  · rw [Iso.symm_hom, Functor.Monoidal.μIso_inv, MonObj.comp_mul, Functor.map_mul, Functor.map_comp,
      Functor.OplaxMonoidal.δ_fst_assoc, Functor.OplaxMonoidal.δ_snd]
  · rw [Iso.symm_hom, Functor.Monoidal.μIso_inv, Functor.OplaxMonoidal.δ_snd]

theorem isPullback_translation_of_cover : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H G : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A) (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) (ψ : ∀ j, (B j).left ⟶ G.left) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) → (∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Q.left) → (∀ j, IsPullback ((fst ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A) ≫ (Over.pullback (𝒰.f j)).map i) * snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (q j) (q j)) → IsPullback ((fst H A ≫ i) * snd H A) (snd H A) Q Q := by
  intro S 𝒰 A H G _ _ i Q B ψ q hψ hq hloc

  let φ : ∀ j, B j ≅ (Over.pullback (𝒰.f j)).obj G := fun j =>
    Over.isoMk (hψ j).isoPullback (by simp)
  have hQ : ∀ j, (Over.pullback (𝒰.f j)).map Q = q j ≫ (φ j).hom := by
    intro j
    ext1
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, Over.comp_left, Category.assoc]
      erw [pullback.lift_fst]
      simp [φ, hq j]
    · simp only [Over.pullback_map_left, Over.comp_left, Category.assoc]
      erw [pullback.lift_snd]
      simp [φ]
  choose e he₁ he₂ using fun j => baseChange_translation (𝒰.f j) A H i
  have w : ((fst H A ≫ i) * snd H A) ≫ Q = snd H A ≫ Q := by
    refine hom_ext_of_pullback_openCover 𝒰 _ _ fun j => ?_
    rw [Functor.map_comp, Functor.map_comp, ← he₁ j, ← he₂ j, hQ j, Category.assoc, Category.assoc,
      (hloc j).w_assoc]
  have hF : ∀ j, IsPullback ((Over.pullback (𝒰.f j)).map ((fst H A ≫ i) * snd H A))
      ((Over.pullback (𝒰.f j)).map (snd H A)) ((Over.pullback (𝒰.f j)).map Q)
      ((Over.pullback (𝒰.f j)).map Q) := by
    intro j
    refine IsPullback.of_iso (hloc j) (e j).symm (Iso.refl _) (Iso.refl _) (φ j) ?_ ?_ ?_ ?_
    · simp [← he₁ j]
    · simp [← he₂ j]
    · simp [hQ j]
    · simp [hQ j]
  let c : H ⊗ A ⟶ pullback Q Q := pullback.lift _ _ w
  have hc : IsIso c := by
    refine isIso_of_pullback_openCover 𝒰 c fun j => ?_
    have hP := (IsPullback.of_hasPullback Q Q).map (Over.pullback (𝒰.f j))
    have : (Over.pullback (𝒰.f j)).map c = ((hF j).isoIsPullback _ _ hP).hom := by
      apply hP.hom_ext
      · rw [IsPullback.isoIsPullback_hom_fst, ← Functor.map_comp]
        exact congrArg (Over.pullback (𝒰.f j)).map (pullback.lift_fst _ _ w)
      · rw [IsPullback.isoIsPullback_hom_snd, ← Functor.map_comp]
        exact congrArg (Over.pullback (𝒰.f j)).map (pullback.lift_snd _ _ w)
    rw [this]
    infer_instance
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) (pullback.lift_fst _ _ w)
    (pullback.lift_snd _ _ w)

end GlobalTheory.GlueQuotPB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedOfIsProjOver
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocExt

theorem isSeparated_of_isProjOver {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Sp R} (h : IsProjOver f) :
    IsSeparated f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsSeparated (PSpace.str R N) := by unfold PSpace.str; infer_instance
  infer_instance

end GlobalTheory.LocExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothColRep
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open scoped TensorProduct

namespace GlobalTheory.SmGL.RowOneCell

def sz (u v : ℕ) (i j : Bool) : ℕ := cond i (cond j v 1) (cond j u 0)

def sigTwo (b : Bool → ℕ) (x y : ℕ) (h0 : b false = x) (h1 : b true = y) :
    (Σ j, Fin (b j)) ≃ Σ j, Two (Fin x) (Fin y) j :=
  Equiv.sigmaCongrRight fun j => match j with
    | false => finCongr h0
    | true => finCongr h1

def rowPart (u v : ℕ) : ∀ i, (Σ j, Fin (sz u v i j)) ≃ Two (Fin u) (Fin (v + 1)) i
  | false => (sigTwo (sz u v false) 0 u rfl rfl).trans (two (stdSum (Nat.zero_add u)))
  | true => (sigTwo (sz u v true) 1 v rfl rfl).trans (two (stdSum (Nat.add_comm 1 v)))

def colPart (u v : ℕ) : ∀ j, (Σ i, Fin (sz u v i j)) ≃ Two (Fin 1) (Fin (u + v)) j
  | false => (sigTwo (fun i => sz u v i false) 0 1 rfl rfl).trans (two (stdSum (Nat.zero_add 1)))
  | true => (sigTwo (fun i => sz u v i true) u v rfl rfl).trans (two (stdSum rfl))

theorem eq_sz {u v : ℕ} (b : Bool → Bool → ℕ)
    (hb : (∀ i, ∑ j, b i j = Fintype.card (Two (Fin u) (Fin (v + 1)) i)) ∧
      ∀ j, ∑ i, b i j = Fintype.card (Two (Fin 1) (Fin (u + v)) j)) (h : b true false = 1) :
    b = sz u v := by
  have r0 := hb.1 false
  have r1 := hb.1 true
  have c0 := hb.2 false
  have c1 := hb.2 true
  simp only [Fintype.sum_bool] at r0 r1 c0 c1
  have e0 : Fintype.card (Two (Fin u) (Fin (v + 1)) false) = u := Fintype.card_fin u
  have e1 : Fintype.card (Two (Fin u) (Fin (v + 1)) true) = v + 1 := Fintype.card_fin _
  have e2 : Fintype.card (Two (Fin 1) (Fin (u + v)) false) = 1 := Fintype.card_fin _
  have e3 : Fintype.card (Two (Fin 1) (Fin (u + v)) true) = u + v := Fintype.card_fin _
  rw [e0] at r0
  rw [e1] at r1
  rw [e2] at c0
  rw [e3] at c1
  funext i j
  cases i <;> cases j <;> simp only [sz, cond_true, cond_false] <;> omega

def extTensorEquiv {G H V W V' W' : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V} {σ : Representation ℂ H W} {ρ' : Representation ℂ G V'}
    {σ' : Representation ℂ H W'} (φ : ρ.Equiv ρ') (ψ : σ.Equiv σ') :
    (extTensor ρ σ).Equiv (extTensor ρ' σ') :=
  .mk (TensorProduct.congr φ.toLinearEquiv ψ.toLinearEquiv) fun g => by
    ext v w
    exact congrArg₂ (fun a b => a ⊗ₜ[ℂ] b) (φ.toIntertwiningMap.isIntertwining _ _ g.1 v)
      (ψ.toIntertwiningMap.isIntertwining _ _ g.2 w)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def colChar (v : ℕ) (χ₂ : kˣ →* ℂˣ) (j : Bool) : kˣ →* ℂˣ :=
  χ₂ * absPow k (cond j (1 / 2) (-(v : ℂ) / 2))

def colRep (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (j : Bool) :
    Representation ℂ (Levi k fun i => Fin (sz u v i j)) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin (sz u v false j)) χ₁) (detRep (Fin (sz u v true j)) (colChar v χ₂ j))).comp
    ((Pi.evalMonoidHom (fun i => GL (Fin (sz u v i j)) k) false).prod
      (Pi.evalMonoidHom (fun i => GL (Fin (sz u v i j)) k) true))

theorem isSmooth_colRep {χ₁ χ₂ : kˣ →* ℂˣ} (h₁ : IsSmoothChar χ₁) (h₂ : IsSmoothChar χ₂) (u v : ℕ) (j : Bool) :
    IsSmooth (colRep χ₁ χ₂ u v j) := by
  refine isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
    ((isSmooth_ofChar_iff _).2 (h₂.mul (GlobalTheory.LocGL.isSmoothChar_absPow _)).detChar)) _ ?_
  exact (continuous_apply false).prodMk (continuous_apply true)

end GlobalTheory.SmGL.RowOneCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardArchimedeanAddCharOfIsStandardTraceAde
section
noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.WeilL2Words.StdArch

theorem supportedAtArchimedean_adeleOfMixedSpaceComponent (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (GlobalTheory.WeilL2Words.arch1 F z) := by
  intro u hu
  have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h, zero_mul]
  · exact mul_zero u.2

theorem evI_arch1 (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (GlobalTheory.WeilL2Words.arch1 F z) = z :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply z

theorem isStdInf_of_isStd : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → GlobalTheory.WeilL2Words.IsStdInf F ψ := by
  intro F _ _ ψ hψ
  refine ⟨-(Algebra.trace ℝ (mixedEmbedding.mixedSpace F)), fun z hz => ?_, fun z => ?_⟩
  · by_contra h
    push_neg at h
    exact hz (GlobalTheory.ArchUniq.Coord.eq_zero_of_trace z fun b => by
      have := h b
      rw [LinearMap.neg_apply, neg_eq_zero] at this
      exact this)
  · rw [hψ.2.2 _ (supportedAtArchimedean_adeleOfMixedSpaceComponent F z), evI_arch1]
    simp only [LinearMap.neg_apply, Complex.ofReal_neg]
    ring_nf

end GlobalTheory.WeilL2Words.StdArch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivApplyEqFoldrDirectionalFderiv
section
open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem iteratedFDeriv_apply_eq_foldr_fderiv :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
    ∀ (j : ℕ) (m : Fin j → E) (x : E),
      iteratedFDeriv ℝ j g x m = (List.ofFn m).foldr (fun v g' => fun z => fderiv ℝ g' z v) g x := by
  intro E _ _ g hg j
  induction j with
  | zero =>
    intro m x
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro m x
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ, List.foldr_cons]
    have hfun : (List.ofFn (fun i : Fin n => m i.succ)).foldr (fun v g' => fun z => fderiv ℝ g' z v) g
        = fun z => iteratedFDeriv ℝ n g z (Fin.tail m) := by
      funext z
      exact (ih (Fin.tail m) z).symm
    simp only [hfun]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) x :=
      (hg.differentiable_iteratedFDeriv (by first | exact_mod_cast ENat.coe_lt_top n | simp | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top n))) x
    rw [fderiv_continuousMultilinear_apply_const_apply hd]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaProductPowAlgebraicModulusOneAll
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

noncomputable section

namespace GlobalTheory.KappaPowMod

theorem algebraicModulusOneAll_one : StandardLatticesGL3.Mod1All 1 := by
  refine ⟨one_mem _, fun σ => ?_⟩
  have e : (⟨1, one_mem _⟩ : TaylorLogMetric.Qbar) = 1 := rfl
  rw [e, map_one, norm_one]

theorem algebraicModulusOneAll_mul {a b : ℂ} (ha : StandardLatticesGL3.Mod1All a) (hb : StandardLatticesGL3.Mod1All b) : StandardLatticesGL3.Mod1All (a * b) := by
  obtain ⟨h1, h1'⟩ := ha
  obtain ⟨h2, h2'⟩ := hb
  refine ⟨mul_mem h1 h2, fun σ => ?_⟩
  have e : (⟨a * b, mul_mem h1 h2⟩ : TaylorLogMetric.Qbar) = ⟨a, h1⟩ * ⟨b, h2⟩ := rfl
  rw [e, map_mul, norm_mul, h1' σ, h2' σ, one_mul]

theorem algebraicModulusOneAll_inv {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) : StandardLatticesGL3.Mod1All a⁻¹ := by
  obtain ⟨h1, h1'⟩ := ha
  refine ⟨inv_mem h1, fun σ => ?_⟩
  have e : (⟨a⁻¹, inv_mem h1⟩ : TaylorLogMetric.Qbar) = (⟨a, h1⟩ : TaylorLogMetric.Qbar)⁻¹ := rfl
  rw [e, map_inv₀, norm_inv, h1' σ, inv_one]

theorem algebraicModulusOneAll_pow {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) (n : ℕ) : StandardLatticesGL3.Mod1All (a ^ n) := by
  induction n with
  | zero => simpa using algebraicModulusOneAll_one
  | succ n ih => rw [pow_succ]; exact algebraicModulusOneAll_mul ih ha

theorem algebraicModulusOneAll_zpow {a : ℂ} (ha : StandardLatticesGL3.Mod1All a) (n : ℤ) : StandardLatticesGL3.Mod1All (a ^ n) := by
  cases n with
  | ofNat n => simpa using algebraicModulusOneAll_pow ha n
  | negSucc n => rw [zpow_negSucc]; exact algebraicModulusOneAll_inv (algebraicModulusOneAll_pow ha _)

def phiQ (D : D7) : D.host.E →+* TaylorLogMetric.Qbar :=
  D.host.φ₀.codRestrict TaylorLogMetric.Qbar fun x => Formalism.L2.KerInert.AlgP.phi_mem_Qbar x

theorem splitPrime_rootChoice_algebraicModulusOneAll {D : D7} {γ₀ : IsoK D} (k : KapChoice γ₀) (p : ℕ) (hp : p.Prime) (hs : SplitK D p) :
    StandardLatticesGL3.Mod1All (k.rt p) := by
  set h := 2 * classNumber D.host.K with hh
  have h0 : h ≠ 0 := mul_ne_zero two_ne_zero (classNumber_ne D)
  set x : D.host.E := (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E) with hx
  set_option synthInstance.maxHeartbeats 200000 in
  have hx0 : x ≠ 0 := by
    have h1 : ((k.pi p : 𝓞 D.host.K) : D.host.K) ≠ 0 := by simpa using k.pi_ne_zero p hp hs
    simpa [hx] using h1
  have hpow := k.rt_pow p hp hs
  have hmem : k.rt p ∈ TaylorLogMetric.Qbar := by
    have hq : k.rt p ^ h ∈ TaylorLogMetric.Qbar := by
      rw [hpow]
      exact div_mem (Formalism.L2.KerInert.AlgP.phi_mem_Qbar _) (Formalism.L2.KerInert.AlgP.phi_mem_Qbar _)
    exact mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := h) (Nat.pos_of_ne_zero h0)
      (mem_algebraicClosure_iff.1 hq))
  refine ⟨hmem, fun σ => ?_⟩
  let ψ : D.host.E →+* ℂ := σ.comp (phiQ D)
  have hc : ψ (D.host.conj x) = starRingEnd ℂ (ψ x) := Formalism.HC.HostAx.conjE_apply _ _ _
  have hψ0 : ψ x ≠ 0 := (map_ne_zero ψ).2 hx0
  have e : (⟨k.rt p, hmem⟩ : TaylorLogMetric.Qbar) ^ h = phiQ D x / phiQ D (D.host.conj x) := by
    apply Subtype.ext
    simp only [IntermediateField.coe_pow, IntermediateField.coe_div]
    exact hpow
  have hn : ‖σ ⟨k.rt p, hmem⟩‖ ^ h = 1 := by
    rw [← norm_pow, ← map_pow, e, map_div₀]
    change ‖ψ x / ψ (D.host.conj x)‖ = 1
    rw [hc, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hψ0)]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) h0).1 hn

theorem kappa_pow_mod1All : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (m : ℕ),
    StandardLatticesGL3.Mod1All (B.kappa ^ m) := by
  intro D cc δ B m
  refine algebraicModulusOneAll_pow ?_ m
  show StandardLatticesGL3.Mod1All (∏ᶠ p : {p : ℕ // p.Prime ∧ SplitK D p}, B.kc.rt p ^ (-(B.kc.yP p)))
  exact finprod_induction StandardLatticesGL3.Mod1All algebraicModulusOneAll_one (fun _ _ => algebraicModulusOneAll_mul)
    fun p => algebraicModulusOneAll_zpow (splitPrime_rootChoice_algebraicModulusOneAll B.kc p p.2.1 p.2.2) _

end GlobalTheory.KappaPowMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDimensionBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_dimension_bound : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (L : Submodule F ((κ → F) × (κ → F))),
    (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank F L ≤ Fintype.card κ := by
  first | exact @GlobalTheory.finrank_le_card_of_isotropic_prod_pi | exact GlobalTheory.finrank_le_card_of_isotropic_prod_pi | (intros; apply GlobalTheory.finrank_le_card_of_isotropic_prod_pi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedFieldPairsEquivDefiniteFieldPairsOddStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markedFieldPairs_equiv_definiteFieldPairs_odd : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (sel : Polynomial G.F → ℂ), IsSel G sel → ∃ e : {q : Cls G // Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol)} ≃ {q : DCls G // Irreducible (Quot.out q).pol}, ∀ q, (Quot.out (e q).1).pol = (Quot.out q.1).pol ∧ ∀ (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → (Quot.out (e q).1).term Kf f r K φ = (Quot.out q.1).term Kf f r K φ := by
  first | (exact @GlobalTheory.LKDef.cls_equiv_dcls_irr) | (exact GlobalTheory.LKDef.cls_equiv_dcls_irr) | (intros; apply GlobalTheory.LKDef.cls_equiv_dcls_irr <;> assumption)
end

