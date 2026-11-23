module

public import Mathlib
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsInvariantNondegeneratePairingWeightRepNabl
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

private theorem exists_Q {ι : Type} [Fintype ι] [DecidableEq ι] {V U : ι → Type} [∀ τ, AddCommGroup (V τ)]
    [∀ τ, Module ℂ (V τ)] [∀ τ, AddCommGroup (U τ)] [∀ τ, Module ℂ (U τ)] [∀ τ, FiniteDimensional ℂ (V τ)]
    (P : ∀ τ, V τ →ₗ[ℂ] U τ →ₗ[ℂ] ℂ) (hP : ∀ τ, Function.Bijective (P τ).flip) :
    ∃ F : (Π τ, V τ) →ₘₗ[ℂ] (PiTensorProduct ℂ U →ₗ[ℂ] ℂ), (∀ u, (∀ v, F v u = 0) → u = 0) ∧
      ∀ v u, F v (PiTensorProduct.tprod ℂ u) = ∏ τ, P τ (v τ) (u τ) := by
  let e : ∀ τ, U τ ≃ₗ[ℂ] Module.Dual ℂ (V τ) := fun τ => LinearEquiv.ofBijective (P τ).flip (hP τ)
  let Q : PiTensorProduct ℂ U ≃ₗ[ℂ] Module.Dual ℂ (PiTensorProduct ℂ V) :=
    (PiTensorProduct.congr e).trans PiTensorProduct.dualDistribEquiv
  refine ⟨(LinearMap.flip Q.toLinearMap).compMultilinearMap (PiTensorProduct.tprod ℂ), fun u hu => ?_, fun v u => ?_⟩
  · apply Q.injective
    rw [map_zero]
    apply PiTensorProduct.ext
    ext v
    exact hu v
  · change PiTensorProduct.dualDistrib (PiTensorProduct.congr e (PiTensorProduct.tprod ℂ u))
      (PiTensorProduct.tprod ℂ v) = _
    rw [PiTensorProduct.congr_tprod, PiTensorProduct.dualDistrib_apply]
    rfl

open Formalism.L2.DIV GlobalTheory.CoefIrred in
theorem UpperTheory.exists_invariant_nondegenerate_pairing_weightRep_nablaT :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ) (lam : ι → DomWeight n),
        (∀ τ (a : Fin n), (lam τ).w a = (mu τ a : ℤ) + sh τ) →
        ∃ P : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] NablaT ℂ n mu →ₗ[ℂ] ℂ, (∀ u, (∀ v, P v u = 0) → u = 0) ∧
          ∀ (g : ι → GL (Fin n) ℂ) v u, P (Formalism.L2.DIV.rhoK lam g v) (wtOp ℂ n mu sh g u) = P v u := by
  intro n ι _ _ mu sh lam hl
  choose P1 hb hi using fun τ =>
    UpperTheory.exists_invariant_perfect_pairing_nablaSq_dualWeyl n (Formalism.CohomologicalDescent.LD.res n (mu τ)) (sh τ) (lam τ) (fun a => hl τ a)
  obtain ⟨F, hF0, hF⟩ := exists_Q P1 hb
  have hUniversal : ∃! P : VV ℂ lam →ₗ[ℂ] NablaT ℂ n mu →ₗ[ℂ] ℂ,
      ∀ w, P (tenMul lam w) = F w := by
    have hBasis : ∀ i, bVV ℂ lam i = tenMul lam (fun τ => ssBasis ℂ (lam τ) (i τ)) := by
      intro i
      apply Subtype.ext
      rw [bVV_coe, tenMul_coe, bVVfun]
      simp only [ssBasis_coe]
    let p := (bVV ℂ lam).constr ℂ (fun i => F (fun τ => ssBasis ℂ (lam τ) (i τ)))
    refine ⟨p, ?_, ?_⟩
    · have hComp : p.compMultilinearMap (tenMul lam) = F := by
        apply Module.Basis.ext_multilinear (fun τ => ssBasis ℂ (lam τ))
        intro i
        simp only [LinearMap.compMultilinearMap_apply, ← hBasis, p, Module.Basis.constr_basis]
      intro w
      exact congrArg (fun m => m w) hComp
    · intro q hq
      apply (bVV ℂ lam).ext
      intro i
      simp only [p, Module.Basis.constr_basis]
      rw [hBasis, hq]
  obtain ⟨P, hP, hUnique⟩ := hUniversal
  refine ⟨P, fun u hu => hF0 u fun v => by rw [← hP]; exact hu _, fun g v u => ?_⟩
  have key : (P ∘ₗ Formalism.L2.DIV.rhoK lam g).compl₂ (wtOp ℂ n mu sh g) = P := by
    refine hUnique _ (fun w => ?_)
    apply PiTensorProduct.ext
    ext x
    change P (Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam w))
      (wtOp ℂ n mu sh g (PiTensorProduct.tprod ℂ x)) = F w (PiTensorProduct.tprod ℂ x)
    rw [rhoK_tenMul, hP, wtOp_apply, GlobalTheory.SemilinTransport.grp_tprod, map_smul, hF, hF]
    simp only [hi]
    rw [Finset.prod_mul_distrib, smul_eq_mul, ← mul_assoc, ← Units.coe_prod, ← Units.val_mul,
      ← Finset.prod_mul_distrib]
    simp
  exact LinearMap.congr_fun (LinearMap.congr_fun key v) u
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsNonzeroVectorValuedEigenformUnitary
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem core {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] {n : ℕ} (F : Frame l ι n) {H : Type} [Group H]
    (e : F.G ≃* H) (io : PadicAlgCl l ≃+* ℂ) (A : H →* (ι → GL (Fin n) (PadicAlgCl l))) (bs : ι → GL (Fin n) (PadicAlgCl l))
    (sh : ι → ℤ) (mu : ι → ℕ → ℕ) (θ : F.I → PadicAlgCl l) (hf : F.IsEig mu θ) :
    ∃ Fm : H → NablaT ℂ n mu, Fm ≠ 0 ∧
      (∀ γ, e.symm γ ∈ F.Γ → ∀ g,
        Fm (γ * g) = wtOp ℂ n mu sh (fun τ => Matrix.GeneralLinearGroup.map io.toRingHom (A γ τ)) (Fm g)) ∧
      (∀ κ : F.K, (∀ τ, Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) = (bs τ)⁻¹ * A (e κ) τ * bs τ) → ∀ c : ℂ,
        io (F.emb (F.chi κ) * ∏ τ, F.emb (F.kap κ τ).val.det ^ sh τ) * c = 1 → ∀ g, Fm (g * e κ) = c • Fm g) ∧
      ∀ i (S : Finset H), (∀ g, g ∈ F.tr i ↔ e g ∈ S) → F.cst i = 1 → (∀ a ∈ S, A a = 1) → ∀ g,
        ∑ a ∈ S, Fm (g * a) = io (θ i) • Fm g := by
  classical
  obtain ⟨f, hf0, ⟨hf1, hf2⟩, hf3⟩ := hf
  obtain ⟨Φ, hΦ, hΦs, hΦw⟩ := UpperTheory.exists_injective_semilinear_nablaT_wtOp_equivariant _ _ io n ι mu sh
  refine ⟨fun g => Φ (wtOp _ n mu sh (A g * bs) (f (e.symm g))), fun h => hf0 ?_, fun γ hγ g => ?_, fun κ hκ c hc g => ?_,
    fun i S hS hc hA g => ?_⟩
  · funext x
    have h1 : Φ (wtOp _ n mu sh (A (e x) * bs) (f (e.symm (e x)))) = 0 := congrFun h (e x)
    rw [e.symm_apply_apply, ← Φ.map_zero] at h1
    have h2 := congrArg (wtOp _ n mu sh (A (e x) * bs)⁻¹) (hΦ h1)
    rw [← Module.End.mul_apply, ← wtOp_mul, inv_mul_cancel, wtOp_one, map_zero] at h2
    exact h2
  · show Φ _ = wtOp _ _ _ _ _ (Φ _)
    rw [← hΦw, map_mul, map_mul, hf1 _ hγ, mul_assoc, wtOp_mul, Module.End.mul_apply]
  · show Φ _ = c • Φ _
    have hk : A (g * e κ) * bs = (A g * bs) * fun τ => Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) := by
      funext τ
      simp only [Pi.mul_apply, map_mul, hκ]
      group
    rw [hk, map_mul, e.symm_apply_apply, wtOp_mul, Module.End.mul_apply, ← hf2 κ (e.symm g),
      wtOp_apply _ _ _ _ (fun τ => Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ)), LinearMap.map_smul, LinearMap.map_smul, hΦs, hΦs, smul_smul]
    congr 1
    have hd : ∀ τ, ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ)) : (PadicAlgCl l)ˣ) :
        PadicAlgCl l) = F.emb (F.kap κ τ).val.det := fun τ => by
      simp [RingHom.map_det]
    simp only [zpow_neg, Finset.prod_inv_distrib, Units.val_inv_eq_inv_val, Units.coe_prod, Units.val_zpow_eq_zpow_val, hd]
    rw [map_mul] at hc
    rw [map_inv₀]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hc]
    ring
  · have h1 : ∑ a ∈ S, f (e.symm g * e.symm a) = ∑ s ∈ F.tr i, f (e.symm g * s) :=
      (Finset.sum_equiv e.toEquiv hS fun s _ => by simp).symm
    have h2 := hf3 i (e.symm g)
    rw [hc, map_one, one_smul, ← h1] at h2
    show ∑ a ∈ S, Φ _ = _ • Φ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hΦs, ← LinearMap.map_smul, ← h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [map_mul, map_mul, hA a ha, mul_one]

set_option maxHeartbeats 800000 in
theorem UpperTheory.exists_nonzero_vectorValued_eigenform_unitary :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime]
        (F : Frame l D.what₂.Tau (Vc D j).rank) (e0 : D.what₂.LL →+* PadicAlgCl l) (ix : F.I → (blk p j t).Pl × ℕ)
        (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)) (T : Tied p j t F e0 ix inc)
        (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl l), F.IsEig mu θ →
        ∃ Fm : Bridge.Gf (Vc D j) → NablaT ℂ (Vc D j).rank mu, Fm ≠ 0 ∧
          (∀ (γ : Formalism.L2.Theta.GQ (Vc D j)) (γ₀ : GL (Fin (Vc D j).rank) D.host.E),
            Formalism.L2.Theta.matHom (Vc D j) γ = Matrix.GeneralLinearGroup.map (Formalism.L2.Theta.incA D) γ₀ → ∀ g,
            Fm (Bridge.ratF (Vc D j) γ * g) = wtOp ℂ (Vc D j).rank mu T.sh
              (fun τ => Matrix.GeneralLinearGroup.map (T.io.toRingHom.comp (inc τ)) γ₀) (Fm g)) ∧
          (∀ (κ : levJ p j t) g, Fm (g * κ) = ((levChi p j t κ : ℂˣ) : ℂ) • Fm g) ∧
          ∀ i, (∀ a ∈ hkA p j t (ix i), GlobalTheory.Hk3.IsLocElt (Vc D j) (plOf p j t (ix i).1) a) → ∀ g,
            ∑ a ∈ hkA p j t (ix i), Fm (g * a) = T.io (θ i) • Fm g := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t l _ F e0 ix inc T mu θ hf
  obtain ⟨A, hA⟩ : ∃ A : Bridge.Gf (Vc D j) →* (D.what₂.Tau → GL (Fin (Vc D j).rank) (PadicAlgCl l)),
      ∀ g τ, (A g τ).val = (matOf j g).map (T.ev τ) :=
    ⟨MonoidHom.pi fun τ => (Matrix.GeneralLinearGroup.map (T.ev τ)).comp (Bridge.Gf (Vc D j)).subtype, fun _ _ => rfl⟩
  obtain ⟨Fm, h0, h1, h2, h3⟩ := core F T.e T.io A T.bs T.sh mu θ hf
  refine ⟨Fm, h0, fun γ γ₀ hγ g => ?_, fun κ g => ?_, fun i hi g => ?_⟩
  · rw [h1 _ ((T.rat _).2 ⟨γ, (T.e.apply_symm_apply _).symm⟩)]
    congr 2
    funext τ
    refine Units.ext (Matrix.ext fun a b => ?_)
    have h4 : (Formalism.L2.Theta.matHom (Vc D j) γ).val a b = Formalism.L2.Theta.incA D (γ₀.val a b) := by rw [hγ]; rfl
    have h5 : matOf j (Bridge.ratF (Vc D j) γ) a b = 1 ⊗ₜ[D.host.F] γ₀.val a b :=
      congrArg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)) h4
    show T.io ((A _ τ).val a b) = T.io (inc τ (γ₀.val a b))
    rw [hA, Matrix.map_apply, h5, T.ev_rat]
  · have hrk : (T.rk : Fin (Vc D j).rank → Fin (Vc D j).rank) = id := by
      rw [Subsingleton.elim T.rk (OrderIso.refl _)]; rfl
    have hk : ∀ (k : F.K) τ, Matrix.GeneralLinearGroup.map F.emb (F.kap k τ) = (T.bs τ)⁻¹ * A (T.e k) τ * T.bs τ := by
      intro k τ
      have h := T.kap k τ
      rw [hrk, Matrix.submatrix_id_id, ← hA, ← Units.val_mul, ← Units.val_mul] at h
      exact Units.ext h
    obtain ⟨κ, hκ⟩ := κ
    obtain ⟨k, rfl⟩ := T.e.surjective κ
    obtain ⟨k', rfl⟩ : ∃ k' : F.K, (k' : F.G) = k := ⟨⟨k, (T.lev k).2 hκ⟩, rfl⟩
    exact h2 k' (hk k') _ (T.chi k' hκ) g
  · refine h3 i _ (T.tr i) (T.cst i) (fun a ha => ?_) g
    funext τ
    exact Units.ext ((hA a τ).trans
      (UpperTheory.eval_localElement_matrix_eq_one_of_prime_not_dvd D (Vc D j) l (T.ev τ) (T.ev_int τ) _ ((T.ix_range _).1 ⟨i, rfl⟩).2.2 a (hi a ha)))
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsSphericalHeckeRepSplitLabelOfOffLevelPlace
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.sum_eq_of_dual_sums {G ι κ : Type} {M : Type} [AddCommGroup M] [Module ℂ M] (R : Finset ι) (B : Finset κ)
    (u : ι → G) (v : κ → G) (Fm : G → M)
    (h : ∀ ℓ : Module.Dual ℂ M, ∑ a ∈ B, ℓ (Fm (v a)) = ∑ γ ∈ R, ℓ (Fm (u γ))) :
    ∑ γ ∈ R, Fm (u γ) = ∑ a ∈ B, Fm (v a) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, map_sum, sub_eq_zero]
  exact (h ℓ).symm

private theorem UpperTheory.dual_invariant_of_trivial_character {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module ℂ M] (J : Subgroup G) (χ : J →* ℂˣ)
    (Fm : G → M) (hF : ∀ (κ : J) g, Fm (g * κ) = ((χ κ : ℂˣ) : ℂ) • Fm g) (ℓ : Module.Dual ℂ M) (g : G) (k : J)
    (hk : χ k = 1) : ℓ (Fm (g * k)) = ℓ (Fm g) := by
  rw [hF, hk, Units.val_one, one_smul]

private theorem UpperTheory.hecke_single_eq_sum {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (F : Bridge.Gf V → ℂ) (g : Bridge.Gf V) :
    GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F g =
      ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) := by
  have e1 : GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F g =
      (1 : ℂ) • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) :=
    Finsupp.sum_single_index
      (h := fun d (z : ℂ) => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ))
      (zero_smul ℂ _)
  exact e1.trans (one_smul ℂ _)

private theorem UpperTheory.level_character_trivial {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hc' : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1) (P : HeightOneSpectrum (𝓞 D.host.E))
    (h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) :
    ∀ y : (levEnv V β L).J, GlobalTheory.Hk3.IsLocElt V P y → (levEnv V β L).χ y = 1 := by
  have hl := fun e f' he => (GlobalTheory.LevSplit.lev_split V β Λ 1 (Formalism.IndefR.Lev.flag1L L) hc').2 P e f' he h1 hoff
  rintro ⟨y, hy⟩ ⟨e, f', a, he, ha, hxa, hs⟩
  obtain rfl : y = (Formalism.L2.Theta.finHom V).rangeRestrict a := Subtype.ext hxa
  exact Units.ext ((hl e f' he).2.1 a ⟨ha, hy⟩ hs)

private theorem UpperTheory.hecke_offprime_sum {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hβ : ∃ c : ℕ, Formalism.IndefR.Lev.IsBaseFrame V β Λ (1 ^ c)) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    (d : List ℤ) (x : Bridge.Gf V) (B : Finset (Bridge.Gf V)) (hd : d.Pairwise (fun a b => b ≤ a))
    (hx : GlobalTheory.Hk3.IsLabElt V P d x) (hB : ∀ a ∈ B, GlobalTheory.Hk3.IsLocElt V P a) (hDC : Bridge.IsDC (levEnv V β L).J x B) :
    ∃ R : Finset (Formalism.L2.Theta.GA D V),
      GlobalTheory.Hk3.SphOp V (Formalism.DivisionValues.conjPl P) (Formalism.IndefR.Mult.dualLab d) R ∧
      ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (Fm : Bridge.Gf V → M),
        (∀ (κ : (levEnv V β L).J) g, Fm (g * κ) = (((levEnv V β L).χ κ : ℂˣ) : ℂ) • Fm g) → ∀ g,
        ∑ γ ∈ R, Fm (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) = ∑ a ∈ B, Fm (g * a) := by
  refine hβ.elim fun c hc => ?_
  have hc' : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hχ := UpperTheory.level_character_trivial V β Λ L hc' P h1 hoff
  have H := _root_.GlobalTheory.HkDict.dcOp_eq_label V β Λ 1 L hc' P h1 hoff d x B hd hx hB hDC
  have hs : GlobalTheory.Hk3.SphOp V (Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P)) d (GlobalTheory.Hk3.rep V P d) := by
    rw [GlobalTheory.SphConj.conjPl_conjPl]
    exact GlobalTheory.SphLabelOps.sphOp_rep H.1
  refine ⟨GlobalTheory.Hk3.rep V P d, GlobalTheory.SphConj.sphOp_conj V _ d _ hs, fun M _ _ Fm hF g => ?_⟩
  refine UpperTheory.sum_eq_of_dual_sums _ _ (fun γ => g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) (fun a => g * a) Fm fun ℓ => ?_
  have h2 := H.2 ℂ (fun h => ℓ (Fm h)) (fun h k hk => UpperTheory.dual_invariant_of_trivial_character _ _ Fm hF ℓ h k (hχ k hk))
  exact (congrFun h2 g).trans (UpperTheory.hecke_single_eq_sum V P d (fun h => ℓ (Fm h)) g)

theorem UpperTheory.exists_sphericalHeckeRep_splitLabel_of_offLevelPlace :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (Q : (blk p j t).Pl) (k : ℕ), 1 ≤ k → k ≤ (Vc D j).rank →
        (∀ a ∈ hkA p j t (Q, k), GlobalTheory.Hk3.IsLocElt (Vc D j) (plOf p j t Q) a) ∧
        ∃ R : Finset (Formalism.L2.Theta.GA D (Vc D j)),
          GlobalTheory.Hk3.SphOp (Vc D j) (labOf p j t Q) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab (Vc D j).rank k)) R ∧
          ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (Fm : Bridge.Gf (Vc D j) → M),
            (∀ (κ : levJ p j t) g, Fm (g * κ) = ((levChi p j t κ : ℂˣ) : ℂ) • Fm g) → ∀ g,
            ∑ γ ∈ R, Fm (g * (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict γ) = ∑ a ∈ hkA p j t (Q, k), Fm (g * a) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t Q k hpos hk
  obtain ⟨hg, -, -⟩ := (GlobalTheory.GoodPrimes.good_primes p.R.toRealDat (p.P.face p.Dcf p.Spf p.Del p.h0 Csz).lv2
    p.charW.base.lev).2.2.2 p.charW.base.fam t Q.1 Q.2
  have hs := fun x => _root_.GlobalTheory.Hk3Split.isLabElt_of_isTEnv (Vc D j) p.R.pl _ ((Q, k) : _ × ℕ) x
  have hloc : ∀ a ∈ hkA p j t (Q, k), GlobalTheory.Hk3.IsLocElt (Vc D j) (plOf p j t Q) a :=
    fun a ha => (hs a).2.1 ((p.R.B.L j t).hecke.hA_loc (Q, k) ⟨hpos, hk⟩ a ha)
  exact ⟨hloc, UpperTheory.hecke_offprime_sum (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) (p.charW.base.lev.βV j) (plOf p j t Q) hg
    _ ((p.R.B.L j t).hecke.hx (Q, k)) (hkA p j t (Q, k)) (hs 1).2.2
    ((hs _).1 hk ((p.R.B.L j t).hecke.hx_ok (Q, k) ⟨hpos, hk⟩)) hloc ((p.R.B.L j t).hecke.hDC (Q, k) ⟨hpos, hk⟩)⟩
end

