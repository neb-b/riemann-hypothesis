module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelScale1
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private theorem adicDD {A Γ : Type} [CommRing A] [TopologicalSpace Γ] {e : ℕ} (t : A) (d : Γ → DD A e)
    (h1 : AdicCont (Ideal.span {t}) fun g => (d g).a)
    (h2 : ∀ k, AdicCont (Ideal.span {t}) fun g => (d g).ep k)
    (h3 : ∀ k, AdicCont (Ideal.span {t}) fun g => (d g).ep' k)
    (h4 : AdicCont (Ideal.span {t}) fun g => (d g).eta) :
    AdicCont (Ideal.span {algebraMap A (DD A e) t}) d := by
  intro N
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have e1 := (h1 N).eventually_eq x
  have e2 := Filter.eventually_all.2 fun k => (h2 k N).eventually_eq x
  have e3 := Filter.eventually_all.2 fun k => (h3 k N).eventually_eq x
  have e4 := (h4 N).eventually_eq x
  filter_upwards [e1, e2, e3, e4] with y a1 a2 a3 a4
  simp only [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at a1 a2 a3 a4 ⊢
  obtain ⟨b1, a1⟩ := a1
  obtain ⟨b4, a4⟩ := a4
  choose b2 a2 using a2
  choose b3 a3 using a3
  refine ⟨⟨b1, b2, b3, b4⟩, ?_⟩
  rw [← map_pow]
  have : algebraMap A (DD A e) (t ^ N) = DD.C (t ^ N) := rfl
  rw [this, sub_eq_add_neg]
  ext <;> simp [-map_pow, a1, a2, a3, a4, sub_eq_add_neg]

private theorem mapInj {X Y : Type} [CommRing X] [CommRing Y] {e : ℕ} (f : X →+* Y) (hf : Function.Injective f) :
    Function.Injective (DD.map (g := e) f) := by
  intro u v h
  have h1 := congrArg DD.a h
  have h2 := congrArg DD.ep h
  have h3 := congrArg DD.ep' h
  have h4 := congrArg DD.eta h
  ext k
  · exact hf h1
  · exact hf (congrFun h2 k)
  · exact hf (congrFun h3 k)
  · exact hf h4

private theorem selLift {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R R' : Type} [CommRing A] [CommRing R] [CommRing R']
    [Algebra A R] [Algebra A R'] (t : A) (f : R →+* R') (hf : Function.Injective f)
    (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)
    (ρ' : F.G₀ → Matrix (Fin n) (Fin n) R') (w' wi' : F.Vl → Matrix (Fin n) (Fin n) R')
    (hρ : ∀ g, (ρ g).map f = ρ' g) (hw : ∀ g, (w g).map f = w' g) (hwi : ∀ g, (wi g).map f = wi' g)
    (V : Submodule A (Matrix (Fin n) (Fin n) R)) (V' : Submodule A (Matrix (Fin n) (Fin n) R'))
    (c : R') (hV : ∀ Z : Matrix (Fin n) (Fin n) R, ∀ Z' ∈ V', Z.map f = c • Z' → Z ∈ V)
    (z' : F.G₀ → Matrix (Fin n) (Fin n) R') (hz' : z' ∈ SelZ F t ρ' w' wi' V')
    (Y' : F.Vl → Matrix (Fin n) (Fin n) R') (hY' : ∀ v, Y' v ∈ V' ∧ LocAt F ρ' w' wi' z' v (Y' v))
    (z : F.G₀ → Matrix (Fin n) (Fin n) R) (hc : ∀ i j, AdicCont (Ideal.span {algebraMap A R t}) fun g => z g i j)
    (hz : ∀ g, (z g).map f = c • z' g) (Y : F.Vl → Matrix (Fin n) (Fin n) R) (hY : ∀ v, (Y v).map f = c • Y' v) :
    z ∈ SelZ F t ρ w wi V := by
  obtain ⟨h1, -, h3, h4, h5, -⟩ := hz'
  have inj : Function.Injective fun Z : Matrix (Fin n) (Fin n) R => Z.map f := Matrix.map_injective hf
  refine ⟨fun g => hV _ _ (h1 g) (hz g), hc, fun g g' => inj ?_, fun g => inj ?_, fun u g hg => inj ?_,
    fun v => ⟨Y v, hV _ _ (hY' v).1 (hY v), fun g => ?_⟩⟩
  · simp only [Matrix.map_add f (map_add f), Matrix.map_mul, hz, hρ, h3, smul_add, Matrix.mul_smul, Matrix.smul_mul]
  · simp only [Matrix.map_neg f (map_neg f), Matrix.transpose_map, hz, h4, smul_neg, Matrix.transpose_smul]
  · simp only [hz, h5 u g hg, smul_zero, Matrix.map_zero f (map_zero f)]
  · have key : (wi v * (z (F.φ v g) - dY F ρ (Y v) (F.φ v g)) * w v).map f =
        c • (wi' v * (z' (F.φ v g) - dY F ρ' (Y' v) (F.φ v g)) * w' v) := by
      simp only [dY, Matrix.map_sub f (map_sub f), Matrix.map_mul, hz, hρ, hw, hwi, hY, ← smul_sub, Matrix.mul_smul,
        Matrix.smul_mul]
    have k2 : ∀ i j, (wi' v * (z' (F.φ v g) - dY F ρ' (Y' v) (F.φ v g)) * w' v) i j = 0 →
        (wi v * (z (F.φ v g) - dY F ρ (Y v) (F.φ v g)) * w v) i j = 0 := by
      intro i j h0
      apply hf
      have := congrFun (congrFun key i) j
      rw [Matrix.map_apply, Matrix.smul_apply, h0, smul_zero] at this
      rw [this, map_zero]
    exact ⟨fun i j hij => k2 i j (((hY' v).2 g).1 i j hij), fun hg i => k2 i i (((hY' v).2 g).2 hg i)⟩

private theorem liftM {K Γ : Type} [Field K] [TopologicalSpace Γ] [Group Γ] [IsTopologicalGroup Γ] {n e : ℕ}
    (z : Γ → Matrix (Fin n) (Fin n) (DD (FractionRing (PowerSeries K)) e)) (hz : BndD (PowerSeries.X : PowerSeries K) z) :
    ∀ᶠ s : ℕ in Filter.atTop, ∃ z' : Γ → Matrix (Fin n) (Fin n) (DD (PowerSeries K) e),
      (∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) (DD (PowerSeries K) e) PowerSeries.X}) fun g => z' g i j) ∧
      ∀ g, (z' g).map (DD.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) =
        (DD.C (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ^ s) : DD (FractionRing (PowerSeries K)) e) • z g := by
  have B := fun φ hφ => Filter.eventually_atTop.2 ((bndOps K Γ).2.2.2.2 φ hφ)
  have e1 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => B _ (hz i j).1
  have e2 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    Filter.eventually_all.2 fun k => B _ ((hz i j).2.1 k)
  have e3 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    Filter.eventually_all.2 fun k => B _ ((hz i j).2.2.1 k)
  have e4 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => B _ (hz i j).2.2.2
  filter_upwards [e1, e2, e3, e4] with s a1 a2 a3 a4
  choose b1 c1 a1 using a1
  choose b2 c2 a2 using a2
  choose b3 c3 a3 using a3
  choose b4 c4 a4 using a4
  refine ⟨fun g => Matrix.of fun i j => ⟨b1 i j g, fun k => b2 i j k g, fun k => b3 i j k g, b4 i j g⟩,
    fun i j => adicDD _ _ (c1 i j) (c2 i j) (c3 i j) (c4 i j), fun g => ?_⟩
  ext i j <;> simp [-map_pow, DD.map, a1, a2, a3, a4]

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.selScale1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ z ∈ Sel1 h x.Fr k, BndD x.t z → ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∃ z' ∈ Sel1 h x.A k, ∀ g, (z' g).map (DD.map (algebraMap x.A x.Fr)) = algebraMap x.A x.Fr x.t ^ s • z g := by
  intro l _ L G G0 h n x k z hz hb
  choose Y hY using hz.2.2.2.2.2
  have c0 := (bndOps x.K G.G₀).1
  have e1 := liftM z hb
  have e2 := Filter.eventually_all.2 fun v => liftM (K := x.K) (fun _ : G.G₀ => Y v)
    fun i j => ⟨c0 _, fun _ => c0 _, fun _ => c0 _, c0 _⟩
  apply Filter.eventually_atTop.1
  filter_upwards [e1, e2] with s a1 a2
  obtain ⟨z', hc, hz'⟩ := a1
  choose Y' _ hY' using a2
  have hf : Function.Injective (algebraMap x.A x.Fr) := IsFractionRing.injective _ _
  have m1 : ∀ M : Matrix (Fin n) (Fin n) x.A, (M.map (algebraMap x.A (DD x.A k.g))).map (DD.map (algebraMap x.A x.Fr)) =
      M.map (algebraMap x.A (DD x.Fr k.g)) := by
    intro M
    ext i j <;> first | rfl | exact map_zero (algebraMap x.A x.Fr)
  have m2 : ∀ Z : Fin k.g → Matrix (Fin n) (Fin n) x.A,
      (DD.epM fun j => (Z j).map (algebraMap x.A x.A)).map (DD.map (algebraMap x.A x.Fr)) =
      DD.epM fun j => (Z j).map (algebraMap x.A x.Fr) := by
    intro Z
    ext i j <;> first | rfl | exact map_zero (algebraMap x.A x.Fr)
  have m0 : (1 : Matrix (Fin n) (Fin n) (DD x.A k.g)).map (DD.map (algebraMap x.A x.Fr)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have p : ∀ (b1 b2 b3 b4 : Bool) (u : DD x.A k.g), ∀ u' ∈ ddPart x.A x.Fr k.g b1 b2 b3 b4,
      DD.map (algebraMap x.A x.Fr) u = DD.C (algebraMap x.A x.Fr x.t ^ s) * u' → u ∈ ddPart x.A x.A k.g b1 b2 b3 b4 := by
    rintro b1 b2 b3 b4 u u' ⟨q1, q2, q3, q4⟩ hu
    refine ⟨fun e => hf ?_, fun e => funext fun j => hf ?_, fun e => funext fun j => hf ?_, fun e => hf ?_⟩
    · simpa [-map_pow, DD.map, q1 e] using congrArg DD.a hu
    · simpa [-map_pow, DD.map, q2 e] using congrFun (congrArg DD.ep hu) j
    · simpa [-map_pow, DD.map, q3 e] using congrFun (congrArg DD.ep' hu) j
    · simpa [-map_pow, DD.map, q4 e] using congrArg DD.eta hu
  refine ⟨z', selLift G.frame x.t (DD.map (algebraMap x.A x.Fr)) (mapInj _ hf) _ _ _ _ _ _ (fun g => ?_) (fun v => ?_) (fun v => ?_)
    _ _ (DD.C (algebraMap x.A x.Fr x.t ^ s)) (fun Z Z' hZ' hZ i j => ?_) z hz Y hY z' hc hz' (fun v => Y' v 1) (fun v => hY' v 1), hz'⟩
  · simp only [Kap.ρ1, NP.ρX, Matrix.map_mul, Matrix.map_add _ (map_add (DD.map (algebraMap x.A x.Fr))), m0, m1, m2]
  · simp only [Kap.w1, NP.wX, Matrix.map_mul, Matrix.map_sub _ (map_sub (DD.map (algebraMap x.A x.Fr))), m0, m1, m2]
  · simp only [Kap.wi1, NP.wiX, Matrix.map_mul, Matrix.map_add _ (map_add (DD.map (algebraMap x.A x.Fr))), m0, m1, m2]
  · have := congrFun (congrFun hZ i) j
    exact ⟨fun e => p _ _ _ _ _ _ ((hZ' i j).1 e) this, fun e => p _ _ _ _ _ _ ((hZ' i j).2 e) this⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TpDual
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem dual_of_univ {R F W : Type} [AddCommGroup R] [Field F] [AddCommGroup W] [Module F W]
    [Module.Finite F W] (π : R →+ W) (T : Submodule F (R →+ F))
    (h1 : ∀ φ : Module.Dual F W, φ.toAddMonoidHom.comp π ∈ T)
    (h2 : ∀ α ∈ T, ∃ φ : Module.Dual F W, φ.toAddMonoidHom.comp π = α) :
    Module.Finite F T ∧ (∀ b, (∀ α ∈ T, α b = 0) → π b = 0) ∧
      ∀ ξ : Module.Dual F T, ∃ w : W, ∀ b, π b = w → ∀ α : T, (α : R →+ F) b = ξ α := by
  let Φ : Module.Dual F W →ₗ[F] T :=
    { toFun := fun φ => ⟨φ.toAddMonoidHom.comp π, h1 φ⟩
      map_add' := fun _ _ => Subtype.ext (by ext; simp)
      map_smul' := fun _ _ => Subtype.ext (by ext; simp) }
  have hΦ : Function.Surjective Φ := fun α => by
    obtain ⟨φ, e⟩ := h2 α.1 α.2
    exact ⟨φ, Subtype.ext e⟩
  refine ⟨Module.Finite.of_surjective Φ hΦ, fun b hb => ?_, fun ξ => ?_⟩
  · exact (Module.forall_dual_apply_eq_zero_iff F (π b)).1 fun φ => hb _ (h1 φ)
  · obtain ⟨w, hw⟩ := (Module.evalEquiv F W).surjective (ξ.comp Φ)
    refine ⟨w, fun b hb α => ?_⟩
    obtain ⟨φ, rfl⟩ := hΦ α
    have := LinearMap.congr_fun hw φ
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearMap.comp_apply] at this
    rw [← this, ← hb]
    rfl

private theorem tp_abs {O R F : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field F] [Algebra O R] [IsLocalHom (algebraMap O R)] (r : R →+* F) (hk : RingHom.ker r = maximalIdeal R)
    (hs : Function.Surjective (r.comp (algebraMap O R))) (I J : Ideal R)
    (hJ : J = (maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2 ⊔ I) (hI : I ≤ maximalIdeal R)
    (hJm : J ≤ maximalIdeal R) (T : Submodule F (R →+ F))
    (hT : ∀ α, α ∈ T ↔ (∀ b b', α (b * b') = r b * α b' + r b' * α b) ∧ (∀ o, α (algebraMap O R o) = 0) ∧
      ∀ b ∈ I, α b = 0) :
    Module.Finite F T ∧ (∀ b ∈ maximalIdeal R, (∀ α ∈ T, α b = 0) → b ∈ J) ∧
      ∀ ξ : Module.Dual F T, ∃ b ∈ maximalIdeal R, ∀ α : T, (α : R →+ F) b = ξ α := by
  have hm : ∀ b, b ∈ maximalIdeal R ↔ r b = 0 := fun b => by rw [← hk, RingHom.mem_ker]
  have hO : ∀ o : O, algebraMap O R o ∈ maximalIdeal R → algebraMap O R o ∈ J := fun o ho => by
    rw [hJ]
    refine Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ?_))
    exact fun hu => ho (hu.map _)
  have hsq : ∀ x ∈ maximalIdeal R, ∀ y ∈ maximalIdeal R, x * y ∈ J := fun x hx y hy => by
    rw [hJ, pow_two]
    exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mul_mem_mul hx hy))
  have hdec : ∀ b : R, ∃ o : O, ∃ x ∈ maximalIdeal R, b = algebraMap O R o + x := fun b => by
    obtain ⟨o, ho⟩ := hs (r b)
    refine ⟨o, b - algebraMap O R o, (hm _).2 ?_, by ring⟩
    rw [map_sub, ← ho]; simp
  let N : Submodule O R := J.restrictScalars O ⊔ 1
  have hNJ : ∀ b ∈ J, N.mkQ b = 0 := fun b hb =>
    (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_sup_left hb)
  have hNO : ∀ o : O, N.mkQ (algebraMap O R o) = 0 := fun o =>
    (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_sup_right (Submodule.mem_one.2 ⟨o, rfl⟩))
  have hkill : ∀ o : O, r (algebraMap O R o) = 0 → ∀ w : R ⧸ N, o • w = 0 := fun o ho w => by
    obtain ⟨b, rfl⟩ := N.mkQ_surjective w
    rw [← map_smul, Algebra.smul_def]
    exact hNJ _ (J.mul_mem_right _ (hO o ((hm _).2 ho)))
  letI : SMul F (R ⧸ N) := ⟨fun c w => Function.surjInv hs c • w⟩
  have hsm : ∀ (o : O) (w : R ⧸ N), (r.comp (algebraMap O R)) o • w = o • w := fun o w => by
    show Function.surjInv hs _ • w = o • w
    rw [← sub_eq_zero, ← sub_smul]
    refine hkill _ ?_ w
    have := Function.surjInv_eq hs ((r.comp (algebraMap O R)) o)
    rw [map_sub, map_sub, sub_eq_zero]
    exact this
  letI : Module F (R ⧸ N) := Function.Surjective.moduleLeft (r.comp (algebraMap O R)) hs hsm
  have hder : ∀ b b' : R, N.mkQ (b * b') = r b • N.mkQ b' + r b' • N.mkQ b := fun b b' => by
    obtain ⟨o, x, hx, rfl⟩ := hdec b
    obtain ⟨o', x', hx', rfl⟩ := hdec b'
    have e : (algebraMap O R o + x) * (algebraMap O R o' + x') =
        algebraMap O R (o * o') + (o • x' + o' • x) + x * x' := by
      simp only [Algebra.smul_def, map_mul]; ring
    have e1 : r (algebraMap O R o + x) = (r.comp (algebraMap O R)) o := by
      rw [map_add (f := _), (hm x).1 hx, add_zero]; rfl
    have e2 : r (algebraMap O R o' + x') = (r.comp (algebraMap O R)) o' := by
      rw [map_add (f := _), (hm x').1 hx', add_zero]; rfl
    rw [e, e1, e2, hsm, hsm]
    simp only [map_add (f := _), hNO, hNJ _ (hsq x hx x' hx'), map_smul, zero_add, add_zero]
  have hsurj : ∀ w : R ⧸ N, ∃ b ∈ maximalIdeal R, N.mkQ b = w := fun w => by
    obtain ⟨b, rfl⟩ := N.mkQ_surjective w
    obtain ⟨o, x, hx, rfl⟩ := hdec b
    exact ⟨x, hx, by rw [map_add (f := _), hNO, zero_add]⟩
  haveI : Module.Finite F (R ⧸ N) := by
    obtain ⟨s, hs'⟩ := IsNoetherian.noetherian (maximalIdeal R)
    refine ⟨Submodule.fg_def.2 ⟨N.mkQ '' s, s.finite_toSet.image _, eq_top_iff.2 fun w _ => ?_⟩⟩
    obtain ⟨b, hb, rfl⟩ := hsurj w
    rw [← hs'] at hb
    induction hb using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
    | smul c x hx ih =>
      rw [hs'] at hx
      rw [smul_eq_mul, hder, (hm x).1 hx, zero_smul, add_zero]
      exact Submodule.smul_mem _ _ (ih trivial)
  obtain ⟨f1, f2, f3⟩ := dual_of_univ (F := F) N.mkQ.toAddMonoidHom T (fun φ => (hT _).2 ⟨fun b b' => by
      show φ (N.mkQ (b * b')) = r b * φ (N.mkQ b') + r b' * φ (N.mkQ b)
      rw [hder, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul], fun o => by
      show φ (N.mkQ _) = 0
      rw [hNO, map_zero], fun b hb => by
      show φ (N.mkQ _) = 0
      rw [hNJ b (by rw [hJ]; exact Ideal.mem_sup_right hb), map_zero]⟩) (fun α hα => by
    obtain ⟨a1, a2, a3⟩ := (hT α).1 hα
    let K : Ideal R :=
      { carrier := {b | r b = 0 ∧ α b = 0}
        add_mem' := fun {x y} hx hy => ⟨by rw [map_add (f := _), hx.1, hy.1, add_zero], by rw [map_add (f := _), hx.2, hy.2, add_zero]⟩
        zero_mem' := ⟨map_zero _, map_zero _⟩
        smul_mem' := fun c x hx => ⟨by rw [smul_eq_mul, map_mul, hx.1, mul_zero],
          by rw [smul_eq_mul, a1, hx.1, hx.2]; ring⟩ }
    have hK : J ≤ K := by
      rw [hJ]
      refine sup_le (sup_le (Ideal.map_le_iff_le_comap.2 fun o ho => ⟨(hm _).1 (hJm ?_), a2 o⟩) ?_)
        fun b hb => ⟨(hm _).1 (hI hb), a3 b hb⟩
      · rw [hJ]; exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ho))
      · rw [pow_two]
        refine Ideal.mul_le.2 fun x hx y hy => ⟨?_, ?_⟩
        · rw [map_mul, (hm x).1 hx, zero_mul]
        · rw [a1, (hm x).1 hx, (hm y).1 hy]; ring
    have hN : ∀ b ∈ N.toAddSubgroup, α b = 0 := fun b hb => by
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (show b ∈ J.restrictScalars O ⊔ 1 from hb)
      obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hz
      rw [map_add (f := _), a2, (hK hy).2, add_zero]
    let ψ : (R ⧸ N) →+ F := QuotientAddGroup.lift N.toAddSubgroup α hN
    have hψ : ∀ b, ψ (N.mkQ b) = α b := fun _ => rfl
    refine ⟨{ toFun := ψ, map_add' := ψ.map_add, map_smul' := fun c w => ?_ }, AddMonoidHom.ext hψ⟩
    obtain ⟨o, rfl⟩ := hs c
    obtain ⟨b, rfl⟩ := N.mkQ_surjective w
    rw [hsm, ← map_smul, hψ, hψ, Algebra.smul_def, a1, a2]
    simp)
  refine ⟨f1, fun b hb h => ?_, fun ξ => ?_⟩
  · have h0 : b ∈ N := (Submodule.Quotient.mk_eq_zero N).1 (f2 b h)
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (show b ∈ J.restrictScalars O ⊔ 1 from h0)
    obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hz
    refine J.add_mem hy (hO o ?_)
    have := (maximalIdeal R).sub_mem hb (hJm hy)
    rwa [add_sub_cancel_left] at this
  · obtain ⟨w, hw⟩ := f3 ξ
    obtain ⟨b, hb, e⟩ := hsurj w
    exact ⟨b, hb, hw b e⟩

theorem UpperTheory.V.Pa.tpDual :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), Module.Finite S.F S.Tp ∧ (∀ b ∈ maximalIdeal S.Bh, (∀ α ∈ S.Tp, α b = 0) → b ∈ S.J2) ∧ ∀ ξ : Module.Dual S.F S.Tp, ∃ b ∈ maximalIdeal S.Bh, ∀ α : S.Tp, (α : S.Bh →+ S.F) b = ξ α := by
  intro l _ S
  haveI : IsNoetherianRing S.Bh := { noetherian := S.d6.noetherian }
  have hI : ired S.U.N ≤ maximalIdeal S.Bh := by
    refine Ideal.span_le.2 ?_
    rintro b ⟨x, hx, y, hy, e⟩
    obtain ⟨c, hc, e'⟩ := S.U.mul_mem x hx y hy
    have : b = c := S.U.inj (e.symm.trans e')
    rw [this]
    exact hc
  have hJ : S.J2 ≤ maximalIdeal S.Bh := by
    refine sup_le (sup_le ?_ (Ideal.pow_le_self two_ne_zero)) hI
    exact ((IsLocalRing.local_hom_tfae (algebraMap S.OO S.Bh)).out 1 3).1
      (IsCO.isLocalHom (O := S.OO) (R := S.Bh))
  exact tp_abs S.rF S.rF_ker S.oo_surj (ired S.U.N) S.J2 rfl hI hJ S.Tp fun _ => Iff.rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TrLatRange
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem trLat_range {A B R : Type} [CommRing A] [CommRing B] [CommRing R] [Algebra A R] [IsNoetherianRing B]
    (φ : B →+* R) (f : B →+* A) (J : Ideal R) (N : ℕ) (hJ : J ^ N = ⊥)
    (h1 : ∀ a, ∃ b, φ b = algebraMap A R a ∧ f b = a) (h2 : ∀ b, φ b - algebraMap A R (f b) ∈ J) :
    ∃ M : Subalgebra A R, (Subalgebra.toSubmodule M).FG ∧ ∀ b, φ b ∈ M := by
  classical
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (RingHom.ker f))
  have hgJ : ∀ i, φ (g i) ∈ J := by
    intro i
    have : g i ∈ RingHom.ker f := hg ▸ Submodule.subset_span ⟨i, rfl⟩
    have h := h2 (g i)
    rwa [(RingHom.mem_ker.1 this), map_zero, sub_zero] at h
  refine ⟨Algebra.adjoin A (Set.range fun i => φ (g i)), ?_, ?_⟩
  · refine fg_adjoin_of_finite (Set.finite_range _) ?_
    rintro _ ⟨i, rfl⟩
    have : φ (g i) ^ N = 0 := by
      have := Ideal.pow_mem_pow (hgJ i) N
      rwa [hJ, Ideal.mem_bot] at this
    exact ⟨Polynomial.X ^ N, Polynomial.monic_X_pow N, by simpa using this⟩
  · have key : ∀ k : ℕ, ∀ b, ∃ m ∈ Algebra.adjoin A (Set.range fun i => φ (g i)), φ b - m ∈ J ^ k := by
      intro k
      induction k with
      | zero => intro b; exact ⟨0, zero_mem _, by simp⟩
      | succ k ih =>
        intro b
        obtain ⟨b', hb', hf⟩ := h1 (f b)
        have hq : b - b' ∈ Submodule.span B (Set.range g) := by
          rw [hg, RingHom.mem_ker, map_sub, hf, sub_self]
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 hq
        choose m hm hm' using ih
        refine ⟨algebraMap A R (f b) + ∑ i, m (c i) * φ (g i), ?_, ?_⟩
        · refine add_mem (Subalgebra.algebraMap_mem _ _) (sum_mem fun i _ => mul_mem (hm _) ?_)
          exact Algebra.subset_adjoin ⟨i, rfl⟩
        · have e : φ b - (algebraMap A R (f b) + ∑ i, m (c i) * φ (g i)) = ∑ i, (φ (c i) - m (c i)) * φ (g i) := by
            have := congrArg φ hc
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sub, map_sum, hb'] at this
            simp only [smul_eq_mul, map_mul] at this
            simp only [sub_mul, Finset.sum_sub_distrib]
            linear_combination -this
          rw [e, pow_succ]
          exact sum_mem fun i _ => Ideal.mul_mem_mul (hm' _) (hgJ i)
    intro b
    obtain ⟨m, hm, h⟩ := key N b
    rw [hJ, Ideal.mem_bot, sub_eq_zero] at h
    rwa [h]

private theorem trLat_pow {A B R : Type} [CommRing A] [CommRing B] [CommRing R] [Algebra A R] [IsLocalRing A]
    [IsLocalRing B] (t : A) (ht : maximalIdeal A ≤ Ideal.span {t})
    (φ : B →+* R) (f : B →+* A) (J : Ideal R) (N : ℕ) (hJ : J ^ N = ⊥)
    (h1 : Function.Surjective f) (h2 : ∀ b, φ b - algebraMap A R (f b) ∈ J) (M : Subalgebra A R) (hM : ∀ b, φ b ∈ M) (j : ℕ) :
    ∀ b ∈ maximalIdeal B ^ (j + N), ∃ y ∈ M, φ b = t ^ j • y := by
  haveI : IsLocalHom f := IsLocalHom.of_surjective f h1
  let φ' : B →+* M := φ.codRestrict M hM
  let J' : Ideal M := J.comap M.val.toRingHom
  have hJ' : J' ^ N = ⊥ := by
    refine le_bot_iff.1 ((Ideal.le_comap_pow _ N).trans ?_)
    rw [hJ]
    intro y hy
    rw [Ideal.mem_comap, Ideal.mem_bot] at hy
    exact Ideal.mem_bot.2 (Subtype.ext hy)
  have hle : (maximalIdeal B).map φ' ≤ Ideal.span {algebraMap A M t} ⊔ J' := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (ht (map_nonunit f b hb))
    rw [Ideal.mem_comap]
    have e : φ' b = algebraMap A M a * algebraMap A M t + (φ' b - algebraMap A M (f b)) := by
      rw [← map_mul, ha]; ring
    rw [e]
    exact add_mem (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_right (h2 b))
  intro b hb
  have h3 : φ' b ∈ ((maximalIdeal B).map φ') ^ (j + N) := by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hb
  have h4 := Ideal.sup_pow_add_le_pow_sup_pow (Ideal.pow_right_mono hle _ h3)
  rw [hJ', sup_bot_eq, Ideal.span_singleton_pow] at h4
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h4
  refine ⟨y, y.2, ?_⟩
  have := congrArg Subtype.val hy
  rw [Algebra.smul_def, map_pow, mul_comm]
  simpa [φ'] using this.symm

private theorem trLat_mul {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (M : Subalgebra A R) (E : Submodule A R) :
    (∀ y ∈ M, ∀ z ∈ Subalgebra.toSubmodule M * E, y * z ∈ Subalgebra.toSubmodule M * E) ∧
      E ≤ Subalgebra.toSubmodule M * E := by
  refine ⟨fun y hy z hz => ?_, fun z hz => ?_⟩
  · have : y * z ∈ Subalgebra.toSubmodule M * (Subalgebra.toSubmodule M * E) := Submodule.mul_mem_mul hy hz
    rwa [← mul_assoc, M.isIdempotentElem_toSubmodule.eq] at this
  · have : 1 * z ∈ Subalgebra.toSubmodule M * E := Submodule.mul_mem_mul M.one_mem hz
    rwa [one_mul] at this

theorem UpperTheory.V.Pa.trLat :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (R : Type) [CommRing R] [Algebra S.F R] [Algebra S.x.A R] [IsScalarTower S.x.A S.F R] (e : R →ₐ[S.F] S.F) (θ : S.U.AA →+* R), S.Test R e θ → ∃ M : Subalgebra S.x.A R, Module.Finite S.x.A M ∧ (∀ b : S.B, θ (algebraMap S.B S.U.AA b) ∈ M) ∧ (∀ g i j, θ (S.U.vr g i j) ∈ M) ∧ (∀ j : ℕ, ∃ j' : ℕ, ∀ b ∈ maximalIdeal S.B ^ j', ∃ y ∈ M, θ (algebraMap S.B S.U.AA b) = S.x.t ^ j • y) ∧ ∃ P : Submodule S.x.A R, P.FG ∧ (∀ p ∈ S.U.P, ∀ i j, θ (p i j) ∈ P) ∧ ∀ y ∈ M, ∀ z ∈ P, y * z ∈ P := by
  intro l _ S R _ _ _ _ e θ T
  classical
  obtain ⟨N, hN⟩ := T.nil
  haveI : Nontrivial R := e.toRingHom.domain_nontrivial
  haveI : IsNoetherianRing S.B := inferInstance
  let φ : S.B →+* R := θ.comp (algebraMap S.B S.U.AA)
  have hφ : ∀ b, φ b = θ (algebraMap S.Bh S.U.AA (algebraMap S.B S.Bh b)) := fun b => by
    rw [← IsScalarTower.algebraMap_apply]; rfl
  have heA : ∀ a : S.x.A, e (algebraMap S.x.A R a) = algebraMap S.x.A S.F a := fun a => by
    rw [IsScalarTower.algebraMap_apply S.x.A S.F R, AlgHom.commutes]; rfl
  have h1 : ∀ a, ∃ b, φ b = algebraMap S.x.A R a ∧ S.P.f.toRingHom b = a := by
    intro a
    obtain ⟨o, b, ho, hb⟩ := S.oo_A a
    refine ⟨b, ?_, hb⟩
    rw [hφ, ← ho, T.oo, ho, S.rF_f, hb, ← IsScalarTower.algebraMap_apply]
  have h2 : ∀ b, φ b - algebraMap S.x.A R (S.P.f.toRingHom b) ∈ RingHom.ker e := by
    intro b
    have this : S.pr0 (algebraMap S.Bh S.U.AA (algebraMap S.B S.Bh b)) = algebraMap S.B S.Bh b := by
      have e : algebraMap S.Bh S.U.AA (S.pr0 (algebraMap S.Bh S.U.AA (algebraMap S.B S.Bh b)) - algebraMap S.B S.Bh b) ∈ S.U.N := by
        have h := (S.pr1 (algebraMap S.Bh S.U.AA (algebraMap S.B S.Bh b))).2
        rw [map_sub]
        convert S.U.N.neg_mem h using 1 <;> simp [Ctx.pr1] <;> ring
      have hz := Submodule.disjoint_def.1 S.U.compl.disjoint _ (Submodule.mem_one.2 ⟨_, rfl⟩) e
      exact sub_eq_zero.1 (S.U.inj (by rw [hz, map_zero]))
    rw [RingHom.mem_ker, map_sub, heA, hφ, T.res, this, S.rF_f, sub_eq_zero]
    rfl
  obtain ⟨M0, hM0, hM0'⟩ := trLat_range φ S.P.f.toRingHom (RingHom.ker e) N hN h1 h2
  obtain ⟨r, p, hp⟩ := Submodule.fg_iff_exists_fin_generating_family.1 S.U.ker_le_span_sub_sup_map
  let E : Submodule S.x.A R := Submodule.span S.x.A (Set.range fun q : Fin r × Fin S.n × Fin S.n => θ (p q.1 q.2.1 q.2.2))
  have hE : E.FG := Submodule.fg_span (Set.finite_range _)
  have hP : ∀ M : Subalgebra S.x.A R, (∀ b, φ b ∈ M) → ∀ z ∈ S.U.P, ∀ i j, θ (z i j) ∈ Subalgebra.toSubmodule M * E := by
    intro M hM z hz i j
    rw [← hp] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      exact (trLat_mul M E).2 (Submodule.subset_span ⟨(k, i, j), rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_apply, map_add (f := _)]; exact add_mem hx hy
    | smul b x _ hx =>
      rw [Matrix.smul_apply, Algebra.smul_def, map_mul]
      exact (trLat_mul M E).1 _ (hM b) _ hx
  let Q : Submodule S.x.A R := Subalgebra.toSubmodule M0 ⊔ Subalgebra.toSubmodule M0 * E
  have hQ : Q.FG := hM0.sup (hM0.mul hE)
  let P0 : Submodule S.x.A R := Q ⊓ ((1 : Submodule S.x.A R) ⊔ (RingHom.ker e).restrictScalars S.x.A)
  have hP0 : P0.FG := hQ.of_le inf_le_left
  have hmem : ∀ y ∈ Q, ∀ a : S.x.A, y - algebraMap S.x.A R a ∈ RingHom.ker e → y ∈ P0 := by
    intro y hy a ha
    refine ⟨hy, Submodule.mem_sup.2 ⟨algebraMap S.x.A R a, Submodule.mem_one.2 ⟨a, rfl⟩, _, ha, by ring⟩⟩
  have hnil : ∀ y ∈ P0, ∃ a : S.x.A, IsNilpotent (y - algebraMap S.x.A R a) := by
    intro y hy
    obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 hy.2
    obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hu
    refine ⟨a, N, ?_⟩
    have := Ideal.pow_mem_pow (I := RingHom.ker e) hz N
    rw [hN, Ideal.mem_bot] at this
    rwa [add_sub_cancel_left]
  have hfin := (adjoin_nil_finite P0 hP0 hnil).1
  have hB : ∀ b, φ b ∈ Algebra.adjoin S.x.A (P0 : Set R) := fun b =>
    Algebra.subset_adjoin (hmem _ (Submodule.mem_sup_left (hM0' b)) _ (h2 b))
  refine ⟨Algebra.adjoin S.x.A (P0 : Set R), hfin, hB, fun g i j => ?_, fun j => ⟨j + N, ?_⟩,
    Subalgebra.toSubmodule (Algebra.adjoin S.x.A (P0 : Set R)) * E, (Module.Finite.iff_fg.1 hfin).mul hE, hP _ hB,
    (trLat_mul _ E).1⟩
  · refine Algebra.subset_adjoin (hmem _ (Submodule.mem_sup_right (hP M0 hM0' _ (S.U.vr_mem g) i j))
      (mat S.x.ρ (S.h.p₀ g) i j) ?_)
    have hvr := S.U.red g i j _ (S.pr1 (S.U.vr g i j)).2
    rw [RingHom.mem_ker, map_sub, heA, T.res, hvr, sub_eq_zero]
  · exact trLat_pow S.x.t PowerSeries.maximalIdeal_eq_span_X.le φ S.P.f.toRingHom (RingHom.ker e) N hN
      (fun a => (h1 a).imp fun _ h => h.2) h2 _ hB j
end

