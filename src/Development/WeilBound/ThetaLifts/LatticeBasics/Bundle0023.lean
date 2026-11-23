module

public import Mathlib
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinV
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0010
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0022
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0018
public import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinC
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ β : Type} [Fintype κ] [Fintype β] {m n : ℕ}

variable {A : Spc F E m} {Y : Spc F E n} {B : Base F E}
  {d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (incM F Y.J)) κ}
  {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (κ ⊕ κ)}
  {om : G2 σ Y →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)} {K : Subgroup (G2 σ Y)}

theorem at_e {W : Type} [AddCommGroup W] [Module (AF F) W] {ι : Type} (e : W ≃ₗ[AF F] (ι → AF F) × (ι → AF F)) {u : W}
    (hu : At (evI F) u) : At (evI F) (e u) := fun s hs => by rw [← map_smul, hu s hs, map_zero]

theorem imp (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) (k : G2 σ Y) :
    Imp B.ψ (om k) fun w => dd.e (actB (cA σ) k (dd.e.symm w)) :=
  ⟨hs.pres k, hs.adm k, fun w w' => by simp only [actB, map_add (f := _), Matrix.add_mul],
    fun c w => by simp only [actB, map_smul, Matrix.smul_mul], fun w φ hφ => by
      have := hs.impl k (dd.e.symm w) φ hφ
      rwa [Darboux.rho, LinearEquiv.apply_symm_apply] at this⟩

theorem om_D (hψ : IsStd B.ψ) (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) (k : G2 σ Y) {u} (hu : At (evI F) u) {Φ}
    (hΦ : Φ ∈ schA F (κ ⊕ κ)) : om k (D (dd.e u) Φ) = D (dd.e (actB (cA σ) k u)) (om k Φ) := by
  have := (imp hs k).inter hψ (at_e dd.e hu) hΦ
  rwa [LinearEquiv.symm_apply_apply] at this

theorem at_actB (k : G2 σ Y) {u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)} (hu : At (evI F) u) : At (evI F) (actB (cA σ) k u) :=
  fun s hs => by rw [actB, ← Matrix.smul_mul, hu s hs, Matrix.zero_mul]

theorem actB_inv (k : G2 σ Y) (u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) : actB (cA σ) k (actB (cA σ) k⁻¹ u) = u := by
  rw [actB, actB, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
  simp


variable (om K) in
def kfin : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ) where
  carrier := {Φ | ∃ N : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ), FiniteDimensional ℂ N ∧ N ≤ schA F _ ∧ Φ ∈ N ∧ ∀ k ∈ K, ∀ Ψ ∈ N, om k Ψ ∈ N}
  zero_mem' := ⟨⊥, inferInstance, bot_le, zero_mem _, fun k _ g hg => by rw [(Submodule.mem_bot ℂ).1 hg, map_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro f g ⟨N, _, h0, h1, h2⟩ ⟨N', _, h0', h1', h2'⟩
    refine ⟨N ⊔ N', inferInstance, sup_le h0 h0', Submodule.add_mem_sup h1 h1', fun k hk g hg => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hg
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h2 k hk x hx) (h2' k hk y hy)
  smul_mem' := fun c _ ⟨N, h, h0, h1, h2⟩ => ⟨N, h, h0, N.smul_mem c h1, h2⟩

theorem D_kfin (hψ : IsStd B.ψ) (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) {u} (hu : At (evI F) u) {Φ}
    (h : Φ ∈ kfin om K) : D (dd.e u) Φ ∈ kfin om K := by
  obtain ⟨N, _, h0, h1, h2⟩ := h
  obtain ⟨N', _, h4⟩ := exists_D_fin N h0
  refine ⟨Submodule.span ℂ {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = D (dd.e v) x},
    Submodule.finiteDimensional_of_le (S₂ := N') (Submodule.span_le.2 ?_), Submodule.span_le.2 ?_,
    Submodule.subset_span ⟨u, hu, Φ, h1, rfl⟩, fun k hk z hz => ?_⟩
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact h4 _ _ x hx
  · rintro _ ⟨v, -, x, hx, rfl⟩
    exact DP_mem (h0 hx) _ _
  · induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, hv, x, hx, rfl⟩ := hz
      exact Submodule.subset_span ⟨_, at_actB k hv, _, h2 k hk x hx, om_D hψ hs k hv (h0 hx)⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ i j => rw [map_add (f := _)]; exact add_mem i j
    | smul c _ _ i => rw [map_smul]; exact Submodule.smul_mem _ _ i

abbrev th2 (Y : Spc F E n) (w : InfinitePlace F) := Matrix.fromBlocks (Y.θ w) 0 0 (-Y.θ w)

theorem vac_kfin (hL : FinLevel) (hB : B.IsGood σ) (hK : IsStab2 B K) (hc : IsCompact (K : Set (G2 σ Y)))
    (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) {ε} {Φ} (hΦ : Φ ∈ schA F (κ ⊕ κ))
    (hv : ∀ u u', At (evI F) u → At (evI F) u' → Rel B.emb ε A.θ (th2 Y) u u' → D (dd.e u') Φ = Complex.I • D (dd.e u) Φ) :
    Φ ∈ kfin om K := by
  obtain ⟨Λ, l1, l2, s, s1, s2⟩ := hL F E σ B m n A Y hB _ dd K hc Φ hΦ
  have radd : ∀ u (x y : (κ ⊕ κ → AF F) → ℂ), dd.rho B.ψ u (x + y) = dd.rho B.ψ u x + dd.rho B.ψ u y := fun u x y =>
    funext fun _ => mul_add _ _ _
  have rsmul : ∀ u (c : ℂ) (x : (κ ⊕ κ → AF F) → ℂ), dd.rho B.ψ u (c • x) = c • dd.rho B.ψ u x := fun u c x =>
    funext fun _ => mul_left_comm _ _ _
  let N : Submodule ℂ ((κ ⊕ κ → AF F) → ℂ) :=
    { carrier := {Ψ | Ψ ∈ schA F _ ∧ (∀ u ∈ Λ, dd.rho B.ψ u Ψ = Ψ) ∧ ∀ u u', At (evI F) u → At (evI F) u' →
        Rel B.emb ε A.θ (th2 Y) u u' → D (dd.e u') Ψ = Complex.I • D (dd.e u) Ψ}
      zero_mem' := ⟨zero_mem _, fun u _ => funext fun _ => mul_zero _, fun _ _ _ _ _ => by simp only [D, DP_zero, smul_zero]⟩
      add_mem' := fun h h' => ⟨add_mem h.1 h'.1, fun u hu => by rw [radd, h.2.1 u hu, h'.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        have e2 := h'.2.2 u u' a b c
        simp only [D] at e1 e2 ⊢
        rw [DP_add h.1 h'.1, DP_add h.1 h'.1, e1, e2, smul_add]⟩
      smul_mem' := fun t _ h => ⟨Submodule.smul_mem _ _ h.1, fun u hu => by rw [rsmul, h.2.1 u hu], fun u u' a b c => by
        have e1 := h.2.2 u u' a b c
        simp only [D] at e1 ⊢
        rw [DP_smul h.1, DP_smul h.1, e1, smul_comm]⟩ }
  refine ⟨N, ?_, fun _ h => h.1, ⟨hΦ, l2, hv⟩, fun k hk Ψ h => ⟨hs.pres k _ h.1, fun u hu => ?_, fun u u' a b c => ?_⟩⟩
  · refine FiniteDimensional.of_injective ((LinearMap.pi fun y : s => LinearMap.proj y.1) ∘ₗ N.subtype)
      ((injective_iff_map_eq_zero _).2 fun Ψ h0 => Subtype.ext (funext fun z => ?_))
    have sp : ∀ x (y : κ ⊕ κ → AF F), (∀ i, evI F (y i) = 0) → pt x 0 + y = pt x (fn y) := fun x y hy => by
      rw [← pt_self (pt x 0 + y), nf_add, nf_pt, show nf y = 0 from funext hy, add_zero]
      exact congrArg (pt x) (funext fun i => zero_add _)
    have z0 : ∀ i, evI F (pt 0 (fn z) i) = 0 := fun i => congrFun (evI_pt 0 (fn z)) i
    have := s2 Ψ.1 Ψ.2.2.1 (pt (nf z) 0) (at_pt _) (fun y hy => ?_) _ z0
    · rwa [sp _ _ z0, show fn (pt 0 (fn z)) = fn z from rfl, pt_self] at this
    obtain ⟨f, e⟩ := slice Ψ.2.1 (fn y)
    have g : Gs dd.e B.emb ε A.θ (th2 Y) f := fun u u' a b c => SchwartzMap.ext fun x => by
      have := congrFun (Ψ.2.2.2 u u' a b c) (pt x (fn y))
      rwa [Pi.smul_apply, D, D, DP_pt e, DP_pt e] at this
    rw [sp _ _ (s1 y hy), e]
    by_cases hf : f = 0
    · rw [hf]; rfl
    obtain ⟨_, hg⟩ := g.gau hB.cm hf
    refine (hg.ne 0 ?_).elim
    rw [← e, ← show nf y = 0 from funext (s1 y hy), pt_self]
    exact congrFun h0 ⟨y, hy⟩
  · rw [← actB_inv k u, ← hs.impl k _ _ h.1, h.2.1 _ ((l1 u hu).2.2 _ (inv_mem hk))]
  · rw [← actB_inv k u, ← actB_inv k u', ← om_D hB.std hs k (at_actB _ a) h.1, ← om_D hB.std hs k (at_actB _ b) h.1, ← map_smul]
    refine congrArg (om k) (h.2.2 _ _ (at_actB _ a) (at_actB _ b) fun w => ?_)
    have cm := (((hK k⁻¹).1 (inv_mem hk)).1 w).eq
    simp only [actB, Matrix.map_mul, Matrix.transpose_map, c w, Matrix.smul_mul, Matrix.mul_assoc, ← Matrix.transpose_mul]
    exact congrArg (fun x => _ • (_ * (_ * xᵀ))) cm

theorem D_box (hψ : IsStd B.ψ) (hd : IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) d' dd) {u₁ u₂} (h1 : At (evI F) u₁)
    (h2 : At (evI F) u₂) (f₁ f₂ : SInf F κ) {g₁ g₂} (s1 : g₁ ∈ SB (κ → Af F)) (s2 : g₂ ∈ SB (κ → Af F)) :
    D (dd.e (Matrix.fromCols u₁ u₂)) (boxFun (pureA F f₁ g₁) (star (pureA F f₂ g₂))) =
      boxFun (pureA F (dd0 (d'.e u₁) f₁) g₁) (star (pureA F f₂ g₂)) + boxFun (pureA F f₁ g₁) (star (pureA F (dd0 (d'.e u₂) f₂) g₂)) := by
  have m1 : pureA F f₁ g₁ ∈ schA F κ := Submodule.subset_span ⟨f₁, g₁, s1, rfl⟩
  have m2 : pureA F f₂ g₂ ∈ schA F κ := Submodule.subset_span ⟨f₂, g₂, s2, rfl⟩
  have h12 : At (evI F) (Matrix.fromCols u₁ u₂) := fun s hs => by
    ext i (j | j)
    exacts [congrFun₂ (h1 s hs) i j, congrFun₂ (h2 s hs) i j]
  funext z
  have a := hasD hψ (at_e dd.e h12) (box_mem m1 m2) z
  have a1 := hasD hψ (at_e d'.e h1) m1 (z ∘ Sum.inl)
  have a2 := (hasD hψ (at_e d'.e h2) m2 (z ∘ Sum.inr)).star
  have b := a1.mul a2
  have sc0 : ∀ {w}, At (evI F) w → ∀ (Ψ : (κ → AF F) → ℂ) x, schr B.ψ (realAd F 0 • w) Ψ x = Ψ x := fun hw Ψ x => by
    rw [← pt_self x, schr_pt hψ hw]; simp [hl]
  simp only [sc0 (at_e d'.e h1), sc0 (at_e d'.e h2), D, DP_pure] at b
  refine a.unique (b.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_))
  have hb := fun s hs => congrArg Prod.snd (at_e d'.e h2 s hs)
  have cj := phase_line B.ψ hψ (d'.e u₂).1 (d'.e u₂).2 (z ∘ Sum.inr) hb t
  have cj' : B.ψ (-((z ∘ Sum.inr) ⬝ᵥ (realAd F t • (d'.e u₂).2) + ⅟(2 : AF F) * ((realAd F t • (d'.e u₂).1) ⬝ᵥ (realAd F t • (d'.e u₂).2)))) =
      star (B.ψ ((z ∘ Sum.inr) ⬝ᵥ (realAd F t • (d'.e u₂).2) + ⅟(2 : AF F) * ((realAd F t • (d'.e u₂).1) ⬝ᵥ (realAd F t • (d'.e u₂).2)))) := by
    rw [AddChar.map_neg_eq_inv, cj, ← Complex.exp_neg, Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  simp only [hd u₁ u₂, schr, boxFun, Pi.mul_apply, Pi.star_apply, star_mul', Prod.smul_fst, Prod.smul_snd, Prod.smul_mk]
  rw [mul_mul_mul_comm, ← cj', ← AddChar.map_add_eq_mul]
  congr 2
  simp only [dotProduct, Fintype.sum_sum_type, Pi.smul_apply, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, Function.comp_apply,
    smul_neg, mul_neg, Finset.sum_neg_distrib]
  ring

theorem box_kfin (hL : FinLevel) (hB : B.IsGood σ) (hK : IsStab2 B K) (hc : IsCompact (K : Set (G2 σ Y)))
    (hs : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) om) (hd : IsDblCoord (cA σ) (-1) (incM F A.J) (incM F Y.J) d' dd)
    {P : Submodule ℂ (SInf F κ)} (hP : ∀ N : Submodule ℂ (SInf F κ), (∀ ε f, Gs d'.e B.emb ε A.θ Y.θ f → f ∈ N) →
      (∀ u, At (evI F) u → ∀ f ∈ N, dd0 (d'.e u) f ∈ N) → P ≤ N) {g₁ g₂} (s1 : g₁ ∈ SB (κ → Af F)) (s2 : g₂ ∈ SB (κ → Af F))
    {f₁ f₂} (h1 : f₁ ∈ P) (h2 : f₂ ∈ P) : boxFun (pureA F f₁ g₁) (star (pureA F f₂ g₂)) ∈ kfin om K := by
  let bx : SInf F κ → SInf F κ → (κ ⊕ κ → AF F) → ℂ := fun f f' => boxFun (pureA F f g₁) (star (pureA F f' g₂))
  have z1 : ∀ f', bx 0 f' = 0 := fun f' => funext fun z => by simp [bx, boxFun, pureA]
  have z2 : ∀ f, bx f 0 = 0 := fun f => funext fun z => by simp [bx, boxFun, pureA]
  have a1 : ∀ f g f', bx (f + g) f' = bx f f' + bx g f' := fun f g f' => funext fun z => by simp [bx, boxFun, pureA, add_mul]
  have a2 : ∀ f f' g, bx f (f' + g) = bx f f' + bx f g := fun f g f' => funext fun z => by simp [bx, boxFun, pureA, add_mul, mul_add]
  have c1 : ∀ (c : ℂ) f f', bx (c • f) f' = c • bx f f' := fun c f f' => funext fun z => by simp [bx, boxFun, pureA, mul_assoc]
  have c2 : ∀ (c : ℂ) f f', bx f (c • f') = star c • bx f f' := fun c f f' => funext fun z => by
    simp [bx, boxFun, pureA]; ring
  have at0 : At (evI F) (0 : Matrix (Fin m) (Fin n) (AE F E)) := fun _ _ => smul_zero _
  have d0 : ∀ f : SInf F κ, dd0 (d'.e 0) f = 0 := fun f => SchwartzMap.ext fun x => by
    simp [dd0, dop_apply, show nf (0 : κ → AF F) = 0 from funext fun _ => evI_zero, linForm_apply]
  have atc : ∀ {u₁ u₂ : Matrix (Fin m) (Fin n) (AE F E)}, At (evI F) u₁ → At (evI F) u₂ → At (evI F) (Matrix.fromCols u₁ u₂) :=
    fun h1 h2 s hs => by
      ext i (j | j)
      exacts [congrFun₂ (h1 s hs) i j, congrFun₂ (h2 s hs) i j]
  have base : ∀ ε f, Gs d'.e B.emb ε A.θ Y.θ f → ∀ ε' f', Gs d'.e B.emb ε' A.θ Y.θ f' → bx f f' ∈ kfin om K := by
    intro ε f hf ε' f' hf'
    by_cases e : f = 0
    · rw [e, z1]; exact zero_mem _
    by_cases e' : f' = 0
    · rw [e', z2]; exact zero_mem _
    have hf'' := hf.same hB.cm hf' e e'
    refine vac_kfin (ε := ε) hL hB hK hc hs (box_mem (Submodule.subset_span ⟨f, g₁, s1, rfl⟩) (Submodule.subset_span ⟨f', g₂, s2, rfl⟩))
      fun u u' a b c => ?_
    have al : ∀ {v : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)}, At (evI F) v → At (evI F) v.toCols₁ ∧ At (evI F) v.toCols₂ := fun h =>
      ⟨fun s hs => Matrix.ext fun i j => congrFun₂ (h s hs) i (.inl j), fun s hs => Matrix.ext fun i j => congrFun₂ (h s hs) i (.inr j)⟩
    have r1 : Rel B.emb ε A.θ Y.θ u.toCols₁ u'.toCols₁ := fun w => Matrix.ext fun i j => by
      have := congrFun₂ (c w) i (.inl j)
      simpa [Matrix.mul_apply, Fintype.sum_sum_type] using this
    have r2 : Rel B.emb ε A.θ Y.θ (-u.toCols₂) u'.toCols₂ := fun w => Matrix.ext fun i j => by
      have := congrFun₂ (c w) i (.inr j)
      simpa [Matrix.mul_apply, Fintype.sum_sum_type] using this
    have n2 : dd0 (d'.e (-u.toCols₂)) f' = -dd0 (d'.e u.toCols₂) f' := SchwartzMap.ext fun x => by
      have ng : ∀ y : κ → AF F, nf (-y) = -nf y := fun y => funext fun i => map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) _
      simp only [dd0, map_neg, Prod.fst_neg, Prod.snd_neg, ng, dop_apply, SchwartzMap.neg_apply, linForm_apply, Pi.neg_apply, mul_neg,
        Finset.sum_neg_distrib]
      push_cast
      ring
    rw [← u.fromCols_toCols, ← u'.fromCols_toCols, D_box hB.std hd (al a).1 (al a).2 f f' s1 s2,
      D_box hB.std hd (al b).1 (al b).2 f f' s1 s2, hf _ _ (al a).1 (al b).1 r1,
      hf'' _ _ (fun s hs => by rw [smul_neg, (al a).2 s hs, neg_zero]) (al b).2 r2, n2, smul_neg, ← neg_smul]
    change bx _ _ + bx _ _ = _ • (bx _ _ + bx _ _)
    rw [c1, c2, smul_add]
    simp
  refine hP ⟨⟨⟨{f' | ∀ f ∈ P, bx f f' ∈ kfin om K}, fun h h' f hf => a2 f _ _ ▸ add_mem (h f hf) (h' f hf)⟩,
    fun f _ => z2 f ▸ zero_mem _⟩, fun c _ h f hf => c2 c f _ ▸ Submodule.smul_mem _ _ (h f hf)⟩ (fun ε' f' hf' => ?_)
    (fun u hu f' h f hf => ?_) h2 f₁ h1
  · refine hP ⟨⟨⟨{f | bx f f' ∈ kfin om K}, fun h h' => by
      rw [Set.mem_setOf_eq, a1]; exact add_mem h h'⟩, by rw [Set.mem_setOf_eq, z1]; exact zero_mem _⟩,
      fun c _ h => by rw [Set.mem_setOf_eq, c1]; exact Submodule.smul_mem _ _ h⟩ (fun ε f hf => base ε f hf ε' f' hf') fun u hu f h => ?_
    have := D_kfin hB.std hs (atc hu at0) h
    rw [D_box hB.std hd hu at0 f f' s1 s2, d0] at this
    change bx _ _ + bx _ _ ∈ _ at this
    rw [z2, add_zero] at this
    exact this
  · have := D_kfin hB.std hs (atc at0 hu) (h f hf)
    rw [D_box hB.std hd at0 hu f f' s1 s2, d0] at this
    change bx _ _ + bx _ _ ∈ _ at this
    rwa [z1, zero_add] at this

end GlobalTheory.ThK.Dbl.Box

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.FinLevel
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Automorphic.GJMatrix GroundTheory.Global GlobalTheory.HeisSchA

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}


variable (F) in
def epsF : AF F := mk 0 1

theorem epsF_mul (t : AF F) : epsF F * t = mk 0 (p2 t) := Prod.ext (zero_mul _) (one_mul _)

theorem epsF_sq : epsF F * epsF F = epsF F := epsF_mul _

theorem evI_epsF (t : AF F) : evI F (epsF F * t) = 0 := by
  rw [epsF_mul]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem epsF_of {t : AF F} (h : evI F t = 0) : epsF F * t = t := by
  rw [epsF_mul]
  exact Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).injective ((map_zero _).trans h.symm)) rfl

theorem level (hψ : Continuous ψ) {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) :
    ∀ᶠ w : (κ → AF F) × (κ → AF F) in 𝓝 0, schr ψ (epsF F • w) Φ = Φ := by
  rw [sch_eq, schwartzBruhatPi_eq_cosetSpanPi] at h
  induction h using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, J, b, rfl⟩ := hG
    have m := finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J (b i)
    have c := continuous_finPartPi (K := F) (ι := κ)
    have h1 : ∀ᶠ w : (κ → AF F) × (κ → AF F) in 𝓝 0, ∀ i, finPartPi w.1 i ∈ idealFiniteAdeles J :=
      eventually_all.2 fun i => ((continuous_apply i).comp (c.comp continuous_fst)).continuousAt.preimage_mem_nhds
        ((isOpen_idealFiniteAdeles J).mem_nhds (zero_mem _))
    have h2 : ∀ᶠ w : (κ → AF F) × (κ → AF F) in 𝓝 0, ∀ z ∈ tsupport (finiteTensor fun i => cosetIndicator J (b i)),
        finChar ψ (z ⬝ᵥ finPartPi w.2 + p2 ⅟(2 : AF F) * (finPartPi w.1 ⬝ᵥ finPartPi w.2)) = 1 :=
      m.2.isCompact.eventually_forall_of_forall_eventually fun z _ => by
        have := ((finChar_isLocallyConstant ψ hψ).comp_continuous (f := fun y : ((κ → AF F) × (κ → AF F)) × (κ → Af F) =>
          y.2 ⬝ᵥ finPartPi y.1.2 + p2 ⅟(2 : AF F) * (finPartPi y.1.1 ⬝ᵥ finPartPi y.1.2)) (by fun_prop)).eventually_eq (0, z)
        simpa [show finPartPi (0 : κ → AF F) = 0 from rfl] using this
    filter_upwards [h1, h2] with w h1 h2
    funext x
    have e1 : infPartPi (x + epsF F • w.1) = infPartPi x := funext fun i => by
      have := evI_epsF (w.1 i)
      exact (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _).trans ((congrArg _ this).trans (add_zero _))
    have e2 : finiteTensor (fun i => cosetIndicator J (b i)) (finPartPi (x + epsF F • w.1)) =
        finiteTensor (fun i => cosetIndicator J (b i)) (finPartPi x) := Finset.prod_congr rfl fun i _ => by
      beta_reduce
      rw [cosetIndicator_apply, cosetIndicator_apply,
        show finPartPi (x + epsF F • w.1) i - b i = finPartPi x i - b i + finPartPi w.1 i from by
          rw [sub_add_eq_add_sub]; exact congrArg (finPartPi x i + · - b i) (one_mul _)]
      simp only [AddSubgroup.add_mem_cancel_right _ (h1 i)]
    simp only [schr, schwartzBruhatTensorPi, Prod.smul_fst, Prod.smul_snd, e1, e2]
    by_cases h0 : finiteTensor (fun i => cosetIndicator J (b i)) (finPartPi x) = 0
    · simp [h0]
    · rw [dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_smul, epsF_sq, smul_eq_mul, smul_eq_mul, mul_left_comm ⅟(2 : AF F),
        ← mul_add, epsF_mul, ← finChar_apply, map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct]
      exact (congrArg (· * _) (h2 _ (subset_tsupport _ h0))).trans (one_mul _)
  | zero => exact .of_forall fun w => funext fun x => mul_zero _
  | add G H _ _ hG hH =>
    filter_upwards [hG, hH] with w hG hH
    funext x
    exact (mul_add _ _ _).trans (congrArg₂ _ (congrFun hG x) (congrFun hH x))
  | smul c G _ hG =>
    filter_upwards [hG] with w hG
    funext x
    exact (mul_left_comm _ _ _).trans (congrArg _ (congrFun hG x))

theorem finite_values (hψ : IsStd ψ) {N : Set ((κ → AF F) × (κ → AF F))} (hN : N ∈ 𝓝 0) :
    ∃ s : Finset (κ → AF F), (∀ y ∈ s, ∀ i, evI F (y i) = 0) ∧ ∀ Ψ : (κ → AF F) → ℂ, (∀ w ∈ N, schr ψ (epsF F • w) Ψ = Ψ) →
      ∀ x : κ → AF F, At (evI F) x → (∀ y ∈ s, Ψ (x + y) = 0) → ∀ y : κ → AF F, (∀ i, evI F (y i) = 0) → Ψ (x + y) = 0 := by
  obtain ⟨ξ, hξ, e⟩ := std_eq hψ
  obtain ⟨N₁, h₁, N₂, h₂, hN⟩ := mem_nhds_prod_iff.1 hN
  have cm : Continuous fun a : Af F => (mk 0 a : AF F) := continuous_const.prodMk continuous_id
  have : ∀ᶠ a : Af F in 𝓝 0, ∀ i, (Pi.single i (mk 0 a) : κ → AF F) ∈ N₂ := eventually_all.2 fun i =>
    ((continuous_single i).comp cm).continuousAt.preimage_mem_nhds (by
      rwa [Function.comp_apply, show (mk 0 0 : AF F) = 0 from rfl, Pi.single_zero])
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset this
  have hC := (isCompact_univ_pi fun _ : κ => isCompact_idealFiniteAdeles (traceDualIdeal F J)).image
    (f := fun y i => (mk 0 (algebraMap F (Af F) ξ⁻¹ * y i) : AF F))
    (continuous_pi fun i => cm.comp (continuous_const.mul (continuous_apply i)))
  obtain ⟨s, hs, hc⟩ := hC.elim_nhds_subcover (fun t => {y | y - t ∈ N₁}) fun t _ =>
    (continuous_sub_right t).continuousAt.preimage_mem_nhds (by rwa [sub_self])
  have hs' : ∀ y ∈ s, ∀ i, evI F (y i) = 0 := fun y hy i => by
    obtain ⟨z, -, rfl⟩ := hs y hy
    exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  refine ⟨s, hs', fun Ψ hΨ x hx h0 y hy => by_contra fun hn => ?_⟩
  have hx0 : epsF F • x = 0 := hx _ (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  refine (fun hm => ?_ : y ∈ _ → False) (hc ⟨fun i => algebraMap F (Af F) ξ * p2 (y i), fun i _ => ?_, ?_⟩)
  · obtain ⟨t, ht, hty⟩ := Set.mem_iUnion₂.1 hm
    have := congrFun (hΨ (y - t, 0) (hN ⟨hty, mem_of_mem_nhds h₂⟩)) (x + t)
    have e : epsF F • (y - t) = y - t := funext fun i => by
      rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, epsF_of (hy i), epsF_of (hs' t ht i)]
    simp [schr, e, h0 t ht, hn] at this
  · refine (forall_finiteAdelicChar_mul_eq_one_iff J _).1 fun a ha => Circle.ext ?_
    have := congrFun (hΨ (0, Pi.single i (mk 0 a)) (hN ⟨mem_of_mem_nhds h₁, hJ ha i⟩)) (x + y)
    simp only [schr, Prod.smul_fst, Prod.smul_snd, smul_zero, zero_dotProduct, mul_zero, add_zero] at this
    rw [mul_eq_right₀ hn, dotProduct_smul, ← smul_dotProduct, smul_add, hx0, zero_add, dotProduct_single, e] at this
    refine Eq.trans (congrArg (fun z => ((adelicChar F z : Circle) : ℂ)) (Prod.ext ?_ ?_)) this
    · exact (mul_zero _).symm.trans (congrArg _ (mul_zero _).symm)
    · show a * (algebraMap F (Af F) ξ * p2 (y i)) = algebraMap F (Af F) ξ * (1 * p2 (y i) * a)
      ring
  · funext i
    beta_reduce
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hξ, map_one, one_mul, ← epsF_mul, epsF_of (hy i)]

theorem finLevel : FinLevel := by
  intro F E _ _ _ _ _ σ B m n A Y hB κ _ dd K hK Φ hΦ
  have lin : ∀ (k : G2 σ Y) (u : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)),
      actB (cA σ) k (epsF F • u) = epsF F • actB (cA σ) k u := fun k u => Matrix.smul_mul _ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : ∀ {α β : Type} [Finite α] [Finite β], IsModuleTopology (AF F) (Matrix α β (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (_ → _ → AE F E))
  have c : Continuous fun y : ((κ → AF F) × (κ → AF F)) × G2 σ Y => dd.e (actB (cA σ) y.2 (dd.e.symm y.1)) :=
    (IsModuleTopology.continuous_of_linearMap dd.e.toLinearMap).comp
      (((IsModuleTopology.continuous_of_linearMap dd.e.symm.toLinearMap).comp continuous_fst).matrix_mul
        (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose)
  obtain ⟨s, hs, h⟩ := finite_values hB.std (hK.eventually_forall_of_forall_eventually
    (P := fun w k => schr B.ψ (epsF F • dd.e (actB (cA σ) k (dd.e.symm w))) Φ = Φ) fun k _ =>
      (c.tendsto' (0, k) 0 (by simp [actB])).eventually (level hB.std.1 hΦ))
  refine ⟨{u | epsF F • u = u ∧ ∀ k ∈ K, dd.rho B.ψ (actB (cA σ) k u) Φ = Φ}, fun u hu => ⟨fun i => ?_, fun i => ?_,
    fun k hk => ⟨by rw [← lin, hu.1], fun k' hk' => ?_⟩⟩, fun u hu => ?_, s, hs, fun Ψ hΨ => h Ψ fun w hw => ?_⟩
  · rw [← hu.1, map_smul]; exact evI_epsF _
  · rw [← hu.1, map_smul]; exact evI_epsF _
  · have := hu.2 _ (mul_mem hk' hk)
    simpa [actB, Matrix.mul_assoc] using this
  · simpa [actB] using hu.2 1 (one_mem _)
  · have := hΨ (epsF F • dd.e.symm w) ⟨by rw [smul_smul, epsF_sq], fun k hk => by
      rw [lin, Darboux.rho, map_smul]; exact hw k hk⟩
    rwa [Darboux.rho, map_smul, LinearEquiv.apply_symm_apply] at this

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.PairsIrrOfArch
section
namespace GlobalTheory.ThK.Dbl

theorem polFinTri : PolFin := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => polFin (PositivityTheory.ThKG.pairV h)

theorem pairsIrr_of_arch (hO : PositivityTheory.ThKF.ArchOp) : PairsIrr :=
  pairsIrr_of PositivityTheory.ThKH.Locrep.locRepEx PositivityTheory.ThKF.pureAct hO polFinTri

end GlobalTheory.ThK.Dbl
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.SchrUnit
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Bad

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open PositivityTheory.ThKG.Loc (idem)
open PositivityTheory.ThKG.Loc.Cone

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing in
theorem sq_ne (ν : @Measure (κ → AF F) (borel _)) (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) {Φ : (κ → AF F) → ℂ}
    (h : Φ ∈ schA F κ) (h0 : Φ ≠ 0) : ∫ u, Φ u * star (Φ u) ∂ν ≠ 0 := fun z => by
  obtain ⟨c, -, hc⟩ := lD_haar ν hν
  have e := hc Φ h Φ h
  have i := (sl_int (box_mem h h) 0).norm
  have ct := GroundTheory.Automorphic.GJMatrix.continuous_of_mem_schwartzBruhatPi h
  have : ∀ u, boxFun Φ (star Φ) (Sum.elim u u) = ((‖Φ u‖ ^ 2 : ℝ) : ℂ) := fun u => by simp [boxFun, Complex.mul_conj']
  rw [z, mul_zero, lD_int (box_mem h h)] at e
  simp only [sl, add_zero, this, Complex.norm_real, norm_pow, norm_norm] at e i
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) i,
    Continuous.ae_eq_iff_eq _ (show Continuous fun x => ‖Φ x‖ ^ 2 from ct.norm.pow 2) continuous_zero] at e
  exact h0 (funext fun u => by simpa using congrFun e u)

theorem norm_eig {G : Type} [Group G] {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} (hu : IsUnitaryOn (adeleClass F) om)
    (hp : ∀ g, ∀ φ ∈ schA F κ, om g φ ∈ schA F κ) {g : G} {Φ} (h : Φ ∈ schA F κ) (h0 : Φ ≠ 0) {c : ℂ} (hc : om g Φ = c • Φ) :
    ‖c‖ = 1 := by
  letI : MeasurableSpace (κ → AF F) := borel _
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨a, a0, ha⟩ := lD_haar (F := F) (κ := κ) Measure.addHaar inferInstance
  have e := lD_unit hu hp g h h
  rw [hc, star_smul, GlobalTheory.SchwartzBox.boxFun_smul_left, GlobalTheory.SchwartzBox.boxFun_smul_right, smul_smul, map_smul, smul_eq_mul,
    mul_eq_right₀ (ha Φ h Φ h ▸ mul_ne_zero (Complex.ofReal_ne_zero.2 a0.ne') (sq_ne _ inferInstance h h0)), Complex.star_def,
    Complex.mul_conj'] at e
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 (by exact_mod_cast e)

theorem schr_unit {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (ν : @Measure (κ → AF F) (borel _))
    (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) (w) (A C : (κ → AF F) → ℂ) :
    ∫ u, schr ψ w A u * star (schr ψ w C u) ∂ν = ∫ u, A u * star (C u) ∂ν := by
  letI : MeasurableSpace (κ → AF F) := borel _
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  rw [← integral_add_right_eq_self (fun u => A u * star (C u)) w.1]
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp only [schr, star_mul']
  rw [mul_mul_mul_comm, Complex.star_def, Complex.mul_conj', GlobalTheory.StdCharFromIsStd.norm_psi hψ]
  simp

open scoped Classical in
theorem ev_adm (x : κ → AF F) : (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := fun g _ =>
  ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => mul_comm _ _⟩

variable {f : SInf F κ} {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hS : ∀ v, φ v ∈ SB _)
  (hs : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
include hS hs

theorem rest_ex (v : Pl F) : ∃ r, Rest (evFin F v) (φ v) r ∧ tens (evFin F v) (φ v) r = pure f φ := by
  classical
  obtain ⟨r, h1, h2⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hs
  have e := h2 (φ v)
  rw [Function.update_eq_self] at e
  exact ⟨r, ⟨h1, e ▸ GlobalTheory.TensUniq.pure_mem_schA f φ hS hs⟩, e⟩

theorem eig {v : Pl F} {S} {c : ℂ} (h : Acts (evFin F v) S (φ v) (c • φ v)) : S (pure f φ) = c • pure f φ := by
  obtain ⟨r, h1, h2⟩ := rest_ex (f := f) hS hs v
  rw [← h2, h r h1]
  exact funext fun x => mul_assoc _ _ _

theorem fix_real {S} (h : Acts (evI F) S f f) : S (pure f φ) = pure f φ := by
  refine h (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hS hs⟩
  refine finprod_congr fun v => congrArg _ (funext fun i => ?_)
  have := congrArg (evFin F v) (congrFun (hz (idem F v) (evI_idem v)) i)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, evFin_idem_self, one_mul, Pi.zero_apply, map_zero] at this
  rw [Pi.add_apply, map_add (f := _), this, add_zero]

theorem fix_box {v : Pl F} {S} (h : Acts (evFin F v) S (boxFun (φ v) (star (φ v))) (boxFun (φ v) (star (φ v)))) :
    S (boxFun (pure f φ) (star (pure f φ))) = boxFun (pure f φ) (star (pure f φ)) := by
  obtain ⟨r, h1, h2⟩ := rest_ex (f := f) hS hs v
  have e : tens (evFin F v) (boxFun (φ v) (star (φ v))) (boxFun r (star r)) = boxFun (pure f φ) (star (pure f φ)) := by
    rw [← h2]
    funext x
    simp only [tens, boxFun, Pi.star_apply, star_mul', Function.comp_def]
    ring
  have m := GlobalTheory.TensUniq.pure_mem_schA f φ hS hs
  rw [← e]
  refine h _ ⟨fun x z hz => ?_, e ▸ box_mem m m⟩
  exact congrArg₂ (fun a b => a * star b) (h1.1 (x ∘ Sum.inl) (z ∘ Sum.inl) fun u hu => congrArg (· ∘ Sum.inl) (hz u hu))
    (h1.1 (x ∘ Sum.inr) (z ∘ Sum.inr) fun u hu => congrArg (· ∘ Sum.inr) (hz u hu))

end GlobalTheory.ThK.Dbl.Bad

end
end

