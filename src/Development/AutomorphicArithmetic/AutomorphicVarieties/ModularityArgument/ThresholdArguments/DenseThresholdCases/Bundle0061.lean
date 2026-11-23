module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0055
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeOperatorPreservesPart

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymOfVieta
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem symOf_act {T W κ : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W]
    (θ : T →* (Module.End ℂ W)ˣ) (t : κ → T) (c : κ → ℂ) :
    ∃ act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W, ∀ a, act (MvPolynomial.X a) = c a • (θ (t a) : Module.End ℂ W) :=
  ⟨(MonoidAlgebra.lift ℂ (Module.End ℂ W) T ((Units.coeHom _).comp θ)).comp
    (MvPolynomial.aeval fun a => MonoidAlgebra.single (t a) (c a)), fun a => by simp⟩
private theorem symOf_int {R R' W W' κ : Type} [CommRing R] [AddCommGroup W] [Module R W] [CommRing R'] [AddCommGroup W']
    [Module R' W'] (Φ : MvPolynomial κ ℤ →+* Module.End R W) (Φ' : MvPolynomial κ ℤ →+* Module.End R' W') (g : W →+ W')
    (h : ∀ a m, Φ' (MvPolynomial.X a) (g m) = g (Φ (MvPolynomial.X a) m)) (F : MvPolynomial κ ℤ) (m : W) :
    Φ' F (g m) = g (Φ F m) := by
  induction F using MvPolynomial.induction_on generalizing m with
  | C r =>
    rw [eq_intCast (MvPolynomial.C : ℤ →+* MvPolynomial κ ℤ), map_intCast, map_intCast, Module.End.intCast_apply,
      Module.End.intCast_apply, map_zsmul]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), hp, hq]
  | mul_X p a hp => rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h, hp]
private theorem symOf_sym {R W W' : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module ℂ W'] {q n : ℕ}
    (c : R →+* ℂ) (act : PU R q n →ₐ[R] Module.End R W) (act' : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Module.End ℂ W') (g : W →+ W')
    (hg : ∀ r m, g (r • m) = c r • g m) (j : Fin q) (N : ℕ) (E : Fin n → Module.End R W) (E' : Fin n → Module.End ℂ W')
    (h : ∀ i, act (MvPolynomial.X (j, i)) = (N : R) ^ (i : ℕ) • E i)
    (h' : ∀ i, act' (MvPolynomial.X i) = (N : ℂ) ^ (i : ℕ) • E' i) (hE : ∀ i m, E' i (g m) = g (E i m)) (k : ℕ) (m : W) :
    act' (MvPolynomial.esymm (Fin n) ℂ k) (g m) = g (act (emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ k)) m) := by
  have h1 := symOf_int (act.toRingHom.comp (emb ℤ R j)) (act'.toRingHom.comp (MvPolynomial.map (Int.castRingHom ℂ))) g
    (fun a m => by
      have e : emb ℤ R j (MvPolynomial.X a) = MvPolynomial.X (j, a) := by simp [emb]
      change act' (MvPolynomial.map _ (MvPolynomial.X a)) _ = g (act (emb ℤ R j (MvPolynomial.X a)) m)
      rw [MvPolynomial.map_X, e, h, h', LinearMap.smul_apply, LinearMap.smul_apply, hg, hE, map_pow, map_natCast])
    (MvPolynomial.esymm (Fin n) ℤ k) m
  rw [RingHom.comp_apply, MvPolynomial.map_esymm] at h1
  exact h1
private theorem symOf_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]
private theorem symOf_vieta {n : ℕ} {A K K' G : Type} [CommRing A] [CommRing K] [CommRing K'] [Group G] (D : GDet n A G)
    (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (hD : D.map f = GDet.ofRep ρ) (e : K →+* K') (g : G) (α : Fin n → K')
    (h : ((ρ g).map e).charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i))) (k : ℕ) (hk : k ≤ n) :
    MvPolynomial.eval α (MvPolynomial.esymm (Fin n) K' k) = e (f (D.lam k (MonoidAlgebra.single g 1))) := by
  have h1 := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 k
  rw [MonoidAlgebra.mapRingHom_single, map_one, hD, GDet.lam, symOf_chi] at h1
  have h2 := Multiset.prod_X_sub_C_coeff (Finset.univ.val.map α) (k := n - k) (by simp)
  rw [Multiset.map_map, Multiset.card_map, Finset.card_val, Finset.card_fin, Nat.sub_sub_self hk] at h2
  rw [← h1, map_mul, ← Polynomial.coeff_map, ← Matrix.charpoly_map, h, ← MvPolynomial.coe_aeval_eq_eval, RingHom.coe_coe,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Finset.prod_eq_multiset_prod]
  erw [h2]
  rw [map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
  simp
private theorem symOf_sph {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {Y : Type} [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ (GL (Fin n) k) Y)
    (σ : SmIrr (GL (Fin n) k)) (hs : IsoSum π ⊤ σ) (y : Y) (hy : y ∈ fixd π (KO k (Fin n))) (h0 : y ≠ 0) :
    IsSpherical σ.ρ := by
  have h1 := isoFix k n Y π σ _ GlobalTheory.SplitFlip.isCompact_KO hs y hy
  unfold IsSpherical IsSphericalFor
  intro h2
  have h3 : ∀ v ∈ fixd σ.ρ (KO k (Fin n)), v = 0 := fun v hv => by
    have h4 : v ∈ GlobalTheory.PRep.fixed σ.ρ (KO k (Fin n)) := fun u => by simpa using hv u u.2
    rw [h2] at h4
    exact (Submodule.mem_bot ℂ).1 h4
  refine h0 ((Submodule.mem_bot ℂ).1 ((iSup_le fun f => ?_ : _ ≤ (⊥ : Submodule ℂ Y)) h1))
  rintro _ ⟨v, hv, rfl⟩
  rw [h3 v hv, map_zero]
  exact zero_mem _
theorem UpperTheory.V.Z.Win.T2.symOf_alt :
    _root_.UpperTheory.V.Pa.Lev.symOf_s_ty := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b V h q w A x δ _ hx _ T ph ta ⟨ι, hsep, hrel⟩ j k hk m hm
  refine Subtype.ext (sub_eq_zero.1 (hsep _ fun y => ?_))
  obtain ⟨Θ, hΘ⟩ := thetaQ L n q w ℂ y.Y y.π (fun _ => ⊤) fun j =>
    (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[(w j).adicCompletion L])).ne').isUnit
  obtain ⟨act, hact⟩ := symOf_act (Θ j) (fun i : Fin n => Pi.mulSingle i (x j)) fun i => (qj w j : ℂ) ^ (i : ℕ)
  let g : fixd A.ρ (UC n w fun _ => ⊤) →+ fixd y.π (UC n w fun _ => ⊤) :=
    { toFun := fun m => ⟨y.sp m, fun u hu => by rw [← y.sp_act, m.2 u hu]⟩
      map_zero' := Subtype.ext (map_zero y.sp)
      map_add' := fun a a' => Subtype.ext (map_add y.sp _ _) }
  have hg : ∀ (r : A.R) m, g (r • m) = ι (y.θ r) • g m := fun r m => Subtype.ext (y.sp_smul r m)
  have hΘg : ∀ t m, (Θ j t).val (g m) = g ((T.Θw j t).val m) := fun t m =>
    Subtype.ext (thetaMap L n q w A.R A.P ℂ y.Y A.ρ y.π _ T.Θw Θ T.hw hΘ y.sp y.sp_act j t m (g m) rfl)
  have h1 := symOf_sym (ι.toRingHom.comp y.θ) T.actw act g hg j (qj w j)
    (fun i => (T.Θw j (Pi.mulSingle i (x j))).val) (fun i => (Θ j (Pi.mulSingle i (x j))).val) (T.actw_u j) hact
    (fun i => hΘg _) k m
  have hfix : ((g m : fixd y.π (UC n w fun _ => ⊤)) : y.Y) ∈ fixd (y.π.comp (atJ n w j)) (KO _ (Fin n)) := fun u hu => by
    change y.π (atJ n w j u) (y.sp m) = y.sp m
    rw [← y.sp_act, hm (atJ n w j u) fun j' _ => ?_]
    by_cases e : j' = j
    · subst e
      simpa [atJ] using hu
    · simp [atJ, Pi.mulSingle_eq_of_ne e]
  by_cases hz : g m = 0
  · have h2 : g (T.actw (emb ℤ A.R j (MvPolynomial.esymm (Fin n) ℤ k)) m) =
        g (A.p.D.lam k (MonoidAlgebra.single (ph j) 1) • m) := by
      rw [← h1, hg, hz, map_zero, smul_zero]
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val h2
  have hsph : IsSpherical (y.σ j).ρ :=
    symOf_sph _ (y.σ j) (y.iso j) _ hfix fun e => hz (Subtype.ext e)
  have h0 := sphScalar hP.gl hP.bz L n q w y.Y y.π Θ hΘ j (y.σ j) (y.iso j) (x j) (hx j) act hact
    (MvPolynomial.esymm (Fin n) ℂ k) (ι (y.θ (A.p.D.lam k (MonoidAlgebra.single (ph j) 1))))
    (MvPolynomial.esymm_isSymmetric _ _ _)
    (fun θ hθ χ hχ => symOf_vieta A.p.D y.θ (mat y.rep) y.det ι.toRingHom (ph j) _
      (((_root_.UpperTheory.V.Z.Win.relT' (hrel y j)) ⊤ le_top θ hθ χ hχ _ fun _ => rfl).1 (Or.inl hsph)) k hk) (g m) hfix
  have h2 := h1.symm.trans (h0.trans (hg _ m).symm)
  rw [map_sub, sub_eq_zero]
  exact congrArg Subtype.val h2
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreSep
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem coreSep_coord {A M N κ : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module ℂ N]
    (Y : Submodule A M) (φ : A →+* ℂ) (sp : M → N) (hadd : ∀ f ∈ Y, ∀ f' ∈ Y, sp (f + f') = sp f + sp f')
    (hsmul : ∀ f ∈ Y, ∀ b : A, sp (b • f) = φ b • sp f) (b : Module.Basis κ A Y)
    (hind : LinearIndependent ℂ fun i => sp (b i)) (g : Y) (hg : sp g = 0) (i : κ) : φ (b.repr g i) = 0 := by
  classical
  let s : Y →ₛₗ[φ] N :=
    { toFun := fun f => sp f
      map_add' := fun f f' => hadd _ f.2 _ f'.2
      map_smul' := fun r f => hsmul _ f.2 r }
  have h1 : s g = ∑ j ∈ (b.repr g).support, φ (b.repr g j) • sp (b j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.linearCombination_repr g, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => s.map_smulₛₗ _ _
  by_cases hi : i ∈ (b.repr g).support
  · exact linearIndependent_iff'.1 hind _ (fun j => φ (b.repr g j)) (h1.symm.trans hg) i hi
  · rw [Finsupp.notMem_support_iff.1 hi, map_zero]
private theorem coreSep_kill {N J : Type*} [AddCommGroup N] [Module ℂ N] (E : Submodule ℂ N) (Y : J → Submodule ℂ N)
    (hE : E = ⨆ j, Y j ⊓ E) (T : Module.End ℂ E) (h : ∀ j, ∀ F : E, (F : N) ∈ Y j → T F = 0) (F : E) : T F = 0 := by
  have hle : E ≤ (LinearMap.ker T).map E.subtype := by
    conv_lhs => rw [hE]
    exact iSup_le fun j G hG => ⟨⟨G, hG.2⟩, h j ⟨G, hG.2⟩ hG.1, rfl⟩
  obtain ⟨G, hG, hGF⟩ := hle F.2
  have : G = F := Subtype.ext hGF
  exact this ▸ hG
theorem UpperTheory.V.Hi.eq_zero_of_vanish_at_good_points_dense_weight :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.AutomorphicHeckeSet ι P →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))], ∀ lam ∈ H.admitted, H.DenseWt θ lam → ∀ t : H.TK θ a K, (∀ x : H.TK θ a K →ₐ[c.O] Qbar l, H.Good θ (x.toRingHom.comp (algebraMap A _)) lam → x t = 0) → t = 0 := by
  intro hLit L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ hθ ι P hP a K _ lam hlam hD t ht
  obtain ⟨-, -, hfree, -⟩ := hiComm L Ω l n c H hAx A θ hθ K
  let b := Module.Free.chooseBasis A (H.X.Ord (H.τA A) θ (H.lev K))
  refine Subtype.ext (LinearMap.ext fun f => ?_)
  let g : H.X.Ord (H.τA A) θ (H.lev K) :=
    ⟨((t : Module.End A (H.MK θ a K)) f : H.MK θ a K), ((t : Module.End A (H.MK θ a K)) f).2.1⟩
  have hg : g = 0 := by
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    refine hD _ fun x hx => ?_
    obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hAx A θ hθ ι x lam hx.2.1
    obtain ⟨h1, act, h2, -, -, -, h3⟩ := _root_.UpperTheory.V.Hi.partAct0_alt hLit L Ω l n c H hAx A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ rfl
    have hE := h1.resolve_right (not_not.2 hx)
    have h0 := coreSep_kill _ _ hE (act t) (fun Y F hF => by
      by_cases hb : Y.1.Y ⊓ Submodule.span ℂ (sp '' H.MK θ a K) = ⊥
      · have : F = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hb _ ⟨hF, F.2⟩)
        rw [this, map_zero]
      · obtain ⟨y, hy, hact⟩ := h3 hx Y.1 hb
        rw [hact t F hF, ht y (hy ▸ hx), map_zero, zero_smul])
      ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩
    have h4 := h2 t f ⟨sp f, Submodule.subset_span ⟨f, f.2, rfl⟩⟩ rfl
    rw [h0] at h4
    have h5 := coreSep_coord _ (ι.toRingHom.comp x.toRingHom) sp (hsp.add K) (hsp.smul K) b (hsp.indep K _ b) g h4.symm i
    exact ι.injective (h5.trans (map_zero ι).symm)
  exact Subtype.ext (congrArg (fun z : H.X.Ord (H.τA A) θ (H.lev K) => (z : H.X.Fn A H.m)) hg)
end
end

