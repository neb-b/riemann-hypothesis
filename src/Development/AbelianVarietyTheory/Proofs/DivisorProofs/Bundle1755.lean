module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicAdelicSchwartzFiniteCosetDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem GlobalTheory.WeilCont.schA_periodic_finite_cosets : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    IsCompact (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ K : Set (κ → FiniteAdeleRing (𝓞 F) F), IsCompact K →
    ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ, (∀ x ∈ L, ∀ z, Ψ (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = Ψ z) →
        (∀ z, Ψ z ≠ 0 → (fun i => (z i).2) ∈ K) →
        ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Ψ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  intro F _ _ κ _ L hLo hLc K hK
  have hcont : ∀ k : κ → FiniteAdeleRing (𝓞 F) F, Continuous fun w : κ → FiniteAdeleRing (𝓞 F) F => w - k :=
    fun k => continuous_id.sub continuous_const
  have hmk : ∀ a b : κ → FiniteAdeleRing (𝓞 F) F,
      (QuotientAddGroup.mk a : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) = QuotientAddGroup.mk b ↔ a - b ∈ L := by
    intro a b
    rw [QuotientAddGroup.eq, ← neg_mem_iff, neg_add, neg_neg, ← sub_eq_add_neg]
  have hfin : (QuotientAddGroup.mk '' K : Set ((κ → FiniteAdeleRing (𝓞 F) F) ⧸ L)).Finite := by
    obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun k => {w | w - k ∈ L})
      (fun k _ => (hLo.preimage (hcont k)).mem_nhds (by simp))
    refine (t.finite_toSet.image QuotientAddGroup.mk).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.mp (hcov hw)
    exact ⟨k, hk, ((hmk w k).2 hwk).symm⟩
  obtain ⟨m, e, he, hS⟩ : ∃ (m : ℕ) (e : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L), Function.Injective e ∧
      ∀ q, q ∈ (QuotientAddGroup.mk '' K : Set ((κ → FiniteAdeleRing (𝓞 F) F) ⧸ L)) ↔ ∃ i, e i = q := by
    refine ⟨hfin.toFinset.card, fun i => (hfin.toFinset.equivFin.symm i).1,
      Subtype.val_injective.comp hfin.toFinset.equivFin.symm.injective, fun q => ⟨fun hq => ?_, ?_⟩⟩
    · exact ⟨hfin.toFinset.equivFin ⟨q, hfin.mem_toFinset.2 hq⟩, by simp⟩
    · rintro ⟨i, rfl⟩
      exact hfin.mem_toFinset.1 (hfin.toFinset.equivFin.symm i).2
  choose y hy using fun i => QuotientAddGroup.mk_surjective (e i)
  refine ⟨m, fun i w => if (QuotientAddGroup.mk w : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) = e i then 1 else 0, y,
    fun i => ?_, fun i j => ?_, ?_⟩
  · refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{w | w - x ∈ L}, hLo.preimage (hcont x), by simp,
      fun x' hx' => ?_⟩, HasCompactSupport.intro' (K := {w | w - y i ∈ L})
      ((Homeomorph.subRight (y i)).isCompact_preimage.2 hLc)
      ((AddSubgroup.isClosed_of_isOpen L hLo).preimage (hcont (y i))) fun w hw => ?_⟩
    · dsimp only
      rw [(hmk x' x).2 hx']
    · dsimp only
      rw [if_neg]
      intro h
      exact hw ((hmk w (y i)).1 (h.trans (hy i).symm))
  · dsimp only
    rw [hy j]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (fun h' => h (he h').symm), if_neg h]
  · intro Ψ hΨ hper hsupp
    choose f hf using fun i => GlobalTheory.WeilCont.exists_slice F hΨ (y i)
    refine ⟨f, funext fun z => ?_⟩
    obtain ⟨x, w, rfl⟩ : ∃ x w, z = GlobalTheory.WeilCont.adeleJoin F x w :=
      ⟨fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2,
        funext fun i => Prod.ext (by simp only [GlobalTheory.WeilCont.adeleJoin, RingEquiv.symm_apply_apply]) rfl⟩
    simp only [Finset.sum_apply, GlobalTheory.WeilCont.pureA_adeleJoin, ← hf]
    by_cases hw : (QuotientAddGroup.mk w : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) ∈ QuotientAddGroup.mk '' K
    · obtain ⟨i0, hi0⟩ := (hS _).1 hw
      rw [Finset.sum_eq_single i0]
      · rw [if_pos hi0.symm, mul_one, hf]
        have hL : w - y i0 ∈ L := (hmk w (y i0)).1 (hi0.symm.trans (hy i0).symm)
        rw [← hper _ hL (GlobalTheory.WeilCont.adeleJoin F x (y i0))]
        congr 1
        funext i
        apply Prod.ext
        · change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i) =
            (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i) +
              (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0
          rw [map_zero, add_zero]
        · change w i = y i0 i + (w i - y i0 i)
          exact (add_sub_cancel _ _).symm
      · intro j _ hj
        rw [if_neg (fun h => hj (he (h.symm.trans hi0.symm))), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have h0 : Ψ (GlobalTheory.WeilCont.adeleJoin F x w) = 0 := by
        by_contra h
        exact hw ⟨w, hsupp _ h, rfl⟩
      rw [h0]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [if_neg, mul_zero]
      intro h
      exact hw (h ▸ (hS _).2 ⟨i, rfl⟩)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPair
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolActsPf

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.RealActs

section Swap

variable {P Q R S : ℕ}

def flipE (P Q R S : ℕ) : Formalism.BasicNotions.TH.Pol R S P Q ≃ₗ[ℂ] Formalism.BasicNotions.TH.Pol P Q R S :=
  (MvPolynomial.renameEquiv ℂ (Equiv.prodComm (Ix R S) (Ix P Q))).toLinearEquiv

theorem flipE_apply (f : Formalism.BasicNotions.TH.Pol R S P Q) : flipE P Q R S f = MvPolynomial.rename Prod.swap f := rfl

theorem lineSign_flip (a : Ix P Q) (b : Ix R S) :
    lineSign (p := R) (q := S) (r := P) (s := Q) b a = lineSign (p := P) (q := Q) (r := R) (s := S) a b := by
  rcases a with a | a <;> rcases b with b | b <;> rfl

theorem flipE_heisOp (c : Matrix (Ix R S) (Ix P Q) ℂ) (f : Formalism.BasicNotions.TH.Pol R S P Q) :
    flipE P Q R S (heisOp c f) = heisOp cᵀ (flipE P Q R S f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [heisOp, flipE_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
    map_smul, map_sum, map_sub, GlobalTheory.FockSwap.rename_raiB, GlobalTheory.FockSwap.rename_lowB]
  congr 1
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l => ?_
  simp [lineSign_flip]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def flipT (ι : Type) (P Q R S : ℕ) :
    (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) ≃ₗ[ℂ] ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S :=
  PiTensorProduct.congr fun _ => flipE P Q R S

theorem flipT_atPl (w : ι) (L' : Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ f, flipE P Q R S (L' f) = L (flipE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    flipT ι P Q R S (atPl w L' T) = atPl w L (flipT ι P Q R S T) := by
  have e : (flipT ι P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (flipT ι P Q R S).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, flipT,
      PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    by_cases hi : i = w
    · subst hi; simp [h]
    · simp [Function.update_of_ne hi]
  exact LinearMap.congr_fun e T

theorem flipT_sumPl (L' : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ w f, flipE P Q R S (L' w f) = L w (flipE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    flipT ι P Q R S (sumPl L' T) = sumPl L (flipT ι P Q R S T) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sumPl, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun w _ => flipT_atPl w (L' w) (L w) (h w) T

end Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isFockMap_flip {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    {P Q R S : ℕ} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w} {JA : Matrix α α (AE F E)}
    {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ}
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ} {A : InfinitePlace F → Matrix α (Ix P Q) ℂ}
    {C : InfinitePlace F → Matrix β (Ix R S) ℂ} {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ} (hΦ : IsFockMap ψ τ d A C Φ)
    (hdd : ∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) :
    IsFockMap ψ τ d' C A (Φ ∘ₗ (flipT (InfinitePlace F) P Q R S).toLinearMap) := by
  refine ⟨hΦ.1.comp (flipT (InfinitePlace F) P Q R S).injective, fun u hu c hc T => ?_⟩
  have hu' : At (evI F) uᵀ := fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]
  have hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ := fun w => by
    rw [Matrix.transpose_map, hc w]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have key := hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (flipT (InfinitePlace F) P Q R S T)
  have hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ) := fun t => by
    show schr ψ (d'.e _) = schr ψ (d.e _)
    rw [← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [flipT_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ) (fun w f => flipE_heisOp (c w) f)]
  set_option backward.isDefEq.respectTransparency false in
   rw [show (fun t : ℝ => d'.rho ψ (realAd F t • u)) =
    (fun t : ℝ => d.rho ψ (realAd F t • uᵀ)) from funext hr]
  exact key

theorem incM_map_real {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem locFin_compact (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

section Graph

variable {κ V : Type} [Fintype κ] [AddCommGroup V] [Module ℂ V] {Φ : V →ₗ[ℂ] SInf F κ}

theorem graph_of_inj (hΦ : Function.Injective Φ) (L : Module.End ℂ V) (Rel : SInf F κ → SInf F κ → Prop)
    (huniq : ∀ f f₁ f₂, Rel f f₁ → Rel f f₂ → f₁ = f₂) (h : ∀ v, Rel (Φ v) (Φ (L v))) :
    ∃ D : SInf F κ →ₗ[ℂ] SInf F κ, (∀ f ∈ LinearMap.range Φ, D f ∈ LinearMap.range Φ) ∧
      ∀ f ∈ LinearMap.range Φ, ∀ f₁ : SInf F κ, Rel f f₁ ↔ f₁ = D f := by
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hΦ)
  refine ⟨Φ ∘ₗ L ∘ₗ Ψ, fun f _ => LinearMap.mem_range_self Φ _, ?_⟩
  rintro _ ⟨v, rfl⟩ f₁
  have e : (Φ ∘ₗ L ∘ₗ Ψ) (Φ v) = Φ (L v) := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.comp_apply Ψ Φ, hΨ, LinearMap.id_apply]
  rw [e]
  exact ⟨fun h1 => huniq _ _ _ h1 (h v), fun h1 => h1 ▸ h v⟩

theorem derOn_of_sd (hΦ : Function.Injective Φ) (L : Module.End ℂ V) (T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (h0 : ∀ t, T t 0 = 0) (h : ∀ v, SD T (Φ v) (Φ (L v))) : DerOn (LinearMap.range Φ) T :=
  graph_of_inj hΦ L (fun f f₁ => ActsD (evI F) T f f₁) (fun f f₁ f₂ => (actsLaws F κ f f₁ f₂).2.2.1 T)
    fun v => (actsLaws F κ _ _ (Φ v)).1 T h0 (h v)

theorem opOn_of_sa (hΦ : Function.Injective Φ) (L : Module.End ℂ V) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (h0 : T 0 = 0) (h : ∀ v, SA T (Φ v) (Φ (L v))) : OpOn (LinearMap.range Φ) T :=
  graph_of_inj hΦ L (fun f f₁ => Acts (evI F) T f f₁) (fun f f₁ f₂ => (actsLaws F κ f f₁ f₂).2.2.2.1 T)
    fun v => (actsLaws F κ _ _ (Φ v)).2.1 T h0 (h v)

end Graph

theorem member (hP : GlobalTheory.FunPr.Hypotheses₂) {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype κ] {P Q R S : ℕ} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w}
    {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {a b : ℂ}
    {A : InfinitePlace F → Matrix α (Ix P Q) ℂ} {C : InfinitePlace F → Matrix β (Ix R S) ℂ}
    {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ} {om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)}
    {θ : InfinitePlace F → Matrix β β ℂ} (hcm : IsCMExt F E σ) (hψ : IsStd ψ) (fr : Framed τ JA JB a b A C)
    (hΦ : IsFockMap ψ τ d A C Φ) (hs : IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om)
    (hθ : ∀ w, θ w * C w = C w * Jm R S) :
    (∀ γ ∈ RLines (σ := σ) JB, DerOn (LinearMap.range Φ) (fun t => om (γ (Multiplicative.ofAdd t)))) ∧
    ∀ k : UG (cA σ) JB, At (evI F) ((k.1 : Matrix β β (AE F E)) - 1) →
      (∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) → OpOn (LinearMap.range Φ) (om k) := by
  have hder : DerEx := _root_.GlobalTheory.HeisDer.derEx
  have hls : LieScalar := _root_.GlobalTheory.LieScal.lieScalar hP hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder)
  have hgen : GenEx := _root_.GlobalTheory.RealLiftGen.genEx
  have hkl : KLine := kLine_of_lineEx exists_line_of_upq
  obtain ⟨c, hact⟩ := hls F E σ _ _ _ _ _ _ _ ψ τ _ _ d a b A C Φ om hcm hψ fr hΦ hs
  refine ⟨fun γ hγ => ?_, fun k hk hc => ?_⟩
  · obtain ⟨Y, -, hY⟩ := hgen F E σ β R S τ JB b C hcm fr.2.2 γ hγ
    exact derOn_of_sd hΦ.1 _ _ (fun t => map_zero _) (hact γ hγ Y hY)
  · obtain ⟨γ, hγ, Y, hY, hKC, hγ1⟩ := hkl F E σ β R S τ JB b C θ hcm fr.2.2 hθ k hk hc
    have hloc := locFin_sumPl _ _ _ (fun w => locFin_compact P Q R S (Y w) (hKC w) (c w * (Y w).trace))
    obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F κ _ Φ _ (om.comp γ) hloc
      (fun t l hl => hs.adm _ l hl) (fun T => hact γ hγ Y hY T)
    change ∀ T, SA (om (γ (Multiplicative.ofAdd 1))) (Φ T) (Φ (U T)) at hSA
    rw [hγ1] at hSA
    exact opOn_of_sa hΦ.1 U _ (map_zero _) hSA

theorem polActs_of_isPair : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → GlobalTheory.RealActs.PolActs B M om := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  have hb := h.base
  have hfr : FrameEx := _root_.GlobalTheory.RealLift.frameEx_holds
  have hder : DerEx := _root_.GlobalTheory.HeisDer.derEx
  have hfe : FockEx := _root_.GlobalTheory.FockMapEx.fockEx_of_derEx hder
  have hpr : PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws actsLaws hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder)
  choose A hA hAθ using fun w => hfr _ _ _ _ _ (h.herm.sig w) (h.herm.cartan w)
  choose C hC hCθ using fun w => hfr _ _ _ _ _ (h.skew.sig w) (h.skew.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_real, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_real]; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have fr' : Framed B.emb (incM F W.J) (incM F X.J) Complex.I 1 C A := ⟨mul_one _, hC1, hA1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := h.weil
  obtain ⟨d', hd', hB⟩ := hwp.2.1
  have hr' : LinearMap.range (Φ ∘ₗ (flipT (InfinitePlace F) r s r' s').toLinearMap) = M.Pol B.ψ B.emb := by
    rw [LinearEquiv.range_comp, hr]
  obtain ⟨h1, h2⟩ := member hP hb.cm hb.std fr' (isFockMap_flip hΦ hd') hB.1 hAθ
  obtain ⟨h3, h4⟩ := member hP hb.cm hb.std fr hΦ hwp.1.1 hCθ
  rw [hr'] at h1 h2
  rw [hr] at h3 h4
  exact ⟨fun γ hγ => h1 γ hγ, fun k hk => h2 k hk.1 hk.2, fun γ hγ => h3 γ hγ, fun k hk => h4 k hk.1 hk.2⟩

end GlobalTheory.PolActsPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjOfNonSplit
section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Formalism.MainNotions.StandardLattice Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO

namespace GlobalTheory.SplitProj

open Filter Topology GlobalTheory.IdemSupport

variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

def spl (ε : AE D) : AE D := ε + cA D ε

variable {ε : AE D}

theorem spl_idem (hε : GlobalTheory.RatAut.IsHalfIdem D ε) : spl ε * spl ε = spl ε := by
  obtain ⟨h1, h2, -, -, -⟩ := hε
  have h3 : cA D ε * cA D ε = cA D ε := by rw [← RingHom.map_mul, h1]
  unfold spl
  linear_combination h1 + h3 + 2 * h2

theorem cA_spl (ε : AE D) : cA D (spl ε) = spl ε := by
  unfold spl; rw [RingHom.map_add (f := _), cA_cA, add_comm]

theorem infPart_spl (hε : GlobalTheory.RatAut.IsHalfIdem D ε) : infPart D (spl ε) = 0 := by
  unfold spl
  rw [RingHom.map_add (f := _), (GlobalTheory.IdemSupport.parts_cA ε).1, hε.2.2.1, RingHom.map_zero, add_zero]

theorem spl_mul_split (hε : GlobalTheory.RatAut.IsHalfIdem D ε) {e : AE D} (he : IsSplitIdem D e) :
    spl ε * (e + cA D e) = e + cA D e := by
  have k1 : ∀ x y : AE D, x * y = 0 → cA D x * cA D y = 0 := fun x y h => by
    rw [← RingHom.map_mul, h, RingHom.map_zero]
  have k2 : ∀ x y : AE D, x * y = y → cA D x * cA D y = cA D y := fun x y h => by
    rw [← RingHom.map_mul, h]
  unfold spl
  rcases hε.2.2.2.1 e he with ⟨a, b⟩ | ⟨a, b⟩
  · have c1 := k2 _ _ a
    have c2 := k1 _ _ b
    rw [cA_cA] at c2
    linear_combination a + b + c1 + c2
  · have c1 := k1 _ _ a
    have c2 := k2 _ _ b
    rw [cA_cA] at c2
    linear_combination a + b + c1 + c2

theorem spl_mul_nonSplit (hε : GlobalTheory.RatAut.IsHalfIdem D ε) {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F}
    (hv : NonSplitAt D v η) : spl ε * algebraMap (AF D.host.F) (AE D) η = 0 := by
  have h := hε.2.2.2.2 v η hv
  have h' : algebraMap (AF D.host.F) (AE D) η * cA D ε = 0 := by
    rw [← GlobalTheory.IdemSupport.cA_algebraMap η, ← RingHom.map_mul, h, RingHom.map_zero]
  unfold spl
  linear_combination h + h'

def pc (hε : GlobalTheory.RatAut.IsHalfIdem D ε) (V : HSp D) (g : GA D V) : GA D V :=
  ⟨piece (spl_idem hε) g.1, piece_mem _ _ (spl_idem hε) (cA_spl ε) g.2⟩

theorem mt_pc (hε : GlobalTheory.RatAut.IsHalfIdem D ε) (V : HSp D) (g : GA D V) :
    mt V (pc hε V g) = spl ε • mt V g + (1 - spl ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

def proj (hε : GlobalTheory.RatAut.IsHalfIdem D ε) (V : HSp D) : GA D V →* GA D V :=
  MonoidHom.mk' (pc hε V) fun g h => mt_inj V (by
    simp only [mt_pc, GlobalTheory.IdemSupport.mt_mul]
    rw [mix_mul (spl_idem hε), one_mul])

variable (hε : GlobalTheory.RatAut.IsHalfIdem D ε) {V : HSp D}
include hε

theorem mt_proj (g : GA D V) :
    mt V (proj hε V g) = spl ε • mt V g + (1 - spl ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := mt_pc hε V g

theorem proj_eq_self {g : GA D V} (hg : ∀ i j, spl ε * (mt V g - 1) i j = (mt V g - 1) i j) : proj hε V g = g :=
  mt_inj V (by
    rw [mt_proj]
    ext i j
    have := hg i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at this ⊢
    linear_combination this)

theorem proj_eq_one {g : GA D V} (hg : ∀ i j, spl ε * (mt V g - 1) i j = 0) : proj hε V g = 1 :=
  mt_inj V (by
    rw [mt_proj, GlobalTheory.IdemSupport.mt_one]
    ext i j
    have := hg i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at this ⊢
    linear_combination this)

theorem proj_mem_GfC (g : GA D V) : proj hε V g ∈ GfC V :=
  mem_GfC_of_suppF V (infPart_spl hε) ((suppF_iff V _ _).2 (smul_mix (spl_idem hε) (mt_proj hε g)))

theorem proj_of_suppAt {g : GA D V} (hg : SuppAt ε V g) : proj hε V g = g := proj_eq_self hε hg

theorem proj_of_split {e : AE D} (he : IsSplitIdem D e) {g : GA D V} (hg : SuppAt e V g) : proj hε V g = g :=
  proj_eq_self hε fun i j => by rw [← hg i j, ← mul_assoc, spl_mul_split hε he]

theorem proj_of_nonSplit {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (hv : NonSplitAt D v η) {g : GA D V}
    (hg : SuppPl η V g) : proj hε V g = 1 :=
  proj_eq_one hε fun i j => by rw [← hg i j, ← mul_assoc, spl_mul_nonSplit hε hv, zero_mul]

theorem proj_of_real {g : GA D V} (hg : g ∈ GinfC V) : proj hε V g = 1 := by
  refine proj_eq_one hε fun i j => GlobalTheory.PlaceIdem.parts_inj D _ _ (by rw [RingHom.map_mul, infPart_spl hε, zero_mul, RingHom.map_zero]) ?_
  have h1 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g) = 1 := congrArg Units.val hg
  have h2 : (finPart D).mapMatrix (Formalism.L2.Theta.mt V g - 1) = 0 := by
    rw [RingHom.map_sub, h1, RingHom.map_one, sub_self]
  have h3 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := congrFun (congrFun h2 i) j
  rw [RingHom.map_mul, h3, mul_zero, RingHom.map_zero]

omit hε in
theorem continuous_mt (V : HSp D) : Continuous fun g : GA D V => mt V g :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_proj : Continuous (proj hε V) := by
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have c1 : Continuous fun g => mt V (proj hε V g) := by
    simp only [mt_proj]
    exact ((continuous_mt V).const_smul (spl ε)).add continuous_const
  have c2 : Continuous fun g => mt V (proj hε V g)⁻¹ := by
    simp only [← map_inv]
    exact c1.comp continuous_inv
  exact continuous_iff_continuousAt.2 fun g =>
    GlobalTheory.LocalGlobalChar.tendsto_HA _ _ _ (c1.tendsto g) (c2.tendsto g)

end GlobalTheory.SplitProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowGoodLatticeNeBot
section
set_option synthInstance.maxHeartbeats 400000
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.CovTop.ne_bot_of_isLattice_coords {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] (M : Submodule O V) {d : ℕ} (hd : 0 < d) (b : Fin d → V) (hb : LinearIndependent K b)
    (hM : Submodule.IsFullLattice K (M.comap ((Fintype.linearCombination K b).restrictScalars O))) : M ≠ ⊥ := by
  rintro rfl
  have hinj : Function.Injective (Fintype.linearCombination K b) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    exact funext (Fintype.linearIndependent_iff.1 hb c (by rwa [Fintype.linearCombination_apply] at hc))
  have h0 : (⊥ : Submodule O V).comap ((Fintype.linearCombination K b).restrictScalars O) = ⊥ := by
    rw [Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.2 hinj
  have h := Submodule.IsFullLattice.span_eq_top (self := hM)
  rw [h0] at h
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  simp at h
end

