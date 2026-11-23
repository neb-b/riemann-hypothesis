module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnrSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.DcMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocEig

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2ActEx
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
section Helpers
open IsLocalRing Matrix UpperTheory.V.Hi
private theorem ae_abs {A R P Lev B ι : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] [Nonempty Lev] [Group B]
    (MK : Lev → Submodule A P) (S : Submodule A P) (op : ι → Module.End A P) (ρ : Representation A B S) (κ : Lev → Subgroup B)
    (hfix : ∀ K, (fixd ρ (κ K)).map S.subtype = MK K) (hex : ∀ f : S, ∃ K, (f : P) ∈ MK K)
    (hinf : ∀ K K', ∃ K'', κ K'' ≤ κ K ∧ κ K'' ≤ κ K') (hconj : ∀ K g, ∃ K', ∀ k ∈ κ K', g⁻¹ * k * g ∈ κ K)
    (hop : ∀ g i (z z' : S), (z' : P) = op i z → (ρ g z' : P) = op i (ρ g z))
    (μ : ∀ K, R →+* Module.End A (MK K))
    (hμ : ∀ K K' (φ : MK K →ₗ[A] MK K'), Function.Injective φ →
      (∀ i (y y' : MK K), (y' : P) = op i y → (φ y' : P) = op i (φ y)) → ∀ t y, φ (μ K t y) = μ K' t (φ y)) :
    ∃ α : R →+* Module.End A S, (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧
      ∀ K t (y : MK K) (z : S), (z : P) = y → (α t z : P) = μ K t y := by
  have hle : ∀ K, MK K ≤ S := fun K => by
    rw [← hfix]
    exact Submodule.map_subtype_le _ _
  have hmem : ∀ K (z : S), (z : P) ∈ MK K ↔ z ∈ fixd ρ (κ K) := fun K z => by
    rw [← hfix]
    exact ⟨fun ⟨y, hy, e⟩ => Subtype.ext e ▸ hy, fun h => ⟨z, h, rfl⟩⟩
  let e : ∀ K, (MK K).comap S.subtype ≃ₗ[A] MK K := fun K => Submodule.comapSubtypeEquivOfLe (hle K)
  have he : ∀ K y, (e K y : P) = (y : S) := fun _ _ => rfl
  have he' : ∀ K y, (((e K).symm y : S) : P) = y := fun K y => by rw [← he, LinearEquiv.apply_symm_apply]
  obtain ⟨α, hα⟩ := levelUR2Glue A R S Lev (fun K => (MK K).comap S.subtype)
    (fun K => (e K).symm.conjRingEquiv.toRingHom.comp (μ K)) hex
    (fun K K' => by
      obtain ⟨K'', h1, h2⟩ := hinf K K'
      exact ⟨K'', fun z hz => (hmem _ z).2 fun k hk => (hmem _ z).1 hz k (h1 hk),
        fun z hz => (hmem _ z).2 fun k hk => (hmem _ z).1 hz k (h2 hk)⟩)
    (fun K K' h t y => by
      have h' : MK K ≤ MK K' := fun x hx => h (x := ⟨x, hle K hx⟩) hx
      have := hμ K K' (Submodule.inclusion h') (Submodule.inclusion_injective h') (fun i y y' hy => hy) t (e K y)
      refine Subtype.ext ?_
      exact (he' K' _).trans ((congrArg Subtype.val this).symm.trans (he' K _).symm))
  have h2 : ∀ K t (y : MK K) (z : S), (z : P) = y → (α t z : P) = μ K t y := fun K t y z hz => by
    have hy : y = e K ⟨z, show (z : P) ∈ MK K from hz ▸ y.2⟩ := Subtype.ext hz.symm
    rw [hy]
    exact (congrArg Subtype.val (hα K t ⟨z, show (z : P) ∈ MK K from hz ▸ y.2⟩)).trans (he' K _)
  refine ⟨α, fun t g z => ?_, h2⟩
  obtain ⟨K, hK⟩ := hex z
  obtain ⟨K', hK'⟩ := hconj K g
  let φ : MK K →ₗ[A] MK K' := (S.subtype ∘ₗ ρ g ∘ₗ Submodule.inclusion (hle K)).codRestrict _ fun y =>
    (hmem K' _).2 fun k hk => by
      have := (hmem K (Submodule.inclusion (hle K) y)).1 y.2 _ (hK' k hk)
      change ρ k (ρ g _) = ρ g _
      conv_rhs => rw [← this]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left]
  have hφ : ∀ y, (φ y : P) = ρ g (Submodule.inclusion (hle K) y) := fun _ => rfl
  have hinj : Function.Injective φ := fun y y' h => by
    have h3 : ρ g (Submodule.inclusion (hle K) y) = ρ g (Submodule.inclusion (hle K) y') :=
      Subtype.ext (by rw [← hφ, ← hφ, h])
    have h4 := congrArg (ρ g⁻¹) h3
    simp only [Representation.inv_self_apply] at h4
    exact Submodule.inclusion_injective _ h4
  have h5 := hμ K K' φ hinj (fun i y y' hy => hop g i _ _ hy) t ⟨z, hK⟩
  refine Subtype.ext ?_
  rw [h2 K' t (φ ⟨z, hK⟩) (ρ g z) rfl, ← h5, hφ]
  exact congrArg (fun x => (ρ g x : P)) (Subtype.ext (h2 K t ⟨z, hK⟩ z rfl).symm)
private theorem ae_ind {Q : Type} [Fintype Q] [DecidableEq Q] {G : Q → Type} [∀ q, Group (G q)] (p : (∀ q, G q) → Prop)
    (h1 : p 1) (hm : ∀ g g', p g → p g' → p (g * g')) (hs : ∀ q g, p (Pi.mulSingle q g)) (g : ∀ q, G q) : p g := by
  rw [← Finset.noncommProd_mulSingle g]
  exact Finset.noncommProd_induction _ _ _ p hm h1 fun q _ => hs q _
private theorem ae_gen {Q : Type} [Fintype Q] [DecidableEq Q] {G : Q → Type} [∀ q, Group (G q)] {A P ι : Type} [CommRing A]
    [AddCommGroup P] [Module A P] (S : Submodule A P) (op : ι → Module.End A P) (ρ : Representation A (∀ q, G q) S)
    (s : ∀ q, G q → Module.End A P) (hρ : ∀ q g f, (ρ (Pi.mulSingle q g) f : P) = s q g f)
    (hop : ∀ q g i, Commute (s q g) (op i)) :
    ∀ g i (z z' : S), (z' : P) = op i z → (ρ g z' : P) = op i (ρ g z) :=
  ae_ind _ (fun i z z' h => by simpa using h)
    (fun g g' hg hg' i z z' h => by
      rw [map_mul]
      exact hg i _ _ (hg' i z z' h))
    (fun q g i z z' h => by rw [hρ, hρ, h, ← Module.End.mul_apply, (hop q g i).eq, Module.End.mul_apply])
section Top
variable {Q : Type} {G : Q → Type} [∀ q, Group (G q)] [∀ q, TopologicalSpace (G q)] [∀ q, IsTopologicalGroup (G q)]
private theorem ae_inf (K K' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))}) :
    ∃ K'' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))},
      Subgroup.pi Set.univ K''.1 ≤ Subgroup.pi Set.univ K.1 ∧ Subgroup.pi Set.univ K''.1 ≤ Subgroup.pi Set.univ K'.1 :=
  ⟨⟨fun q => K.1 q ⊓ K'.1 q, fun q => ⟨(K.2 q).1.inter (K'.2 q).1,
      (K.2 q).2.inter_right ((K'.1 q).isClosed_of_isOpen (K'.2 q).1)⟩⟩,
    fun _ hk q hq => (hk q hq).1, fun _ hk q hq => (hk q hq).2⟩
private theorem ae_conj (K : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))})
    (g : ∀ q, G q) : ∃ K' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))},
      ∀ k ∈ Subgroup.pi Set.univ K'.1, g⁻¹ * k * g ∈ Subgroup.pi Set.univ K.1 :=
  ⟨⟨fun q => (K.1 q).comap (MulAut.conj (g q)⁻¹).toMonoidHom, fun q => by
      let e := (Homeomorph.mulLeft (g q)⁻¹).trans (Homeomorph.mulRight (g q)⁻¹⁻¹)
      exact ⟨(K.2 q).1.preimage e.continuous, e.isCompact_preimage.2 (K.2 q).2⟩⟩,
    fun k hk q hq => by simpa using hk q hq⟩
end Top
private theorem ae_commU {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (u : X.Ub) (b : Gp) : Commute (X.ra τ u) (X.U A m b) := by
  unfold Frame.U Iwa.uOp
  refine finsum_induction (fun t => Commute (X.ra τ u) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun q => ?_
  refine LinearMap.ext fun f => funext fun g => ?_
  change (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * ((u : Ga), 1) * (1, _)) =
    (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * (1, _) * ((u : Ga), 1))
  simp [mul_assoc]
private theorem ae_dc {A H H' M : Type} [CommRing A] [Group H] [Group H'] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (s : H' →* H) (u : H) (h : ∀ g, Commute u (s g)) (K K' : Subgroup H') (x : H') :
    Commute (ρ u) (dc (ρ.comp s) K K' x) :=
  finsum_induction (fun t => Commute (ρ u) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun _ => (h _).map ρ
private theorem ae_bot {A R P : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] {Y : Submodule A P} (h : Y = ⊥)
    (lam : A → R) : ∃ μ : R →+* Module.End A Y, (∀ b y, μ (lam b) y = b • y) ∧ Subsingleton Y := by
  haveI : Subsingleton Y := h ▸ inferInstance
  exact ⟨⟨⟨⟨fun _ => 0, Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩, rfl, fun _ _ => Subsingleton.elim _ _⟩,
    fun _ _ => Subsingleton.elim _ _, this⟩
private theorem ae_mu {O A R P ι : Type} [CommRing O] [CommRing A] [CommRing R] [AddCommGroup P] [Module A P]
    {Y : Submodule A P} {op : ι → Module.End A P} [Fact (CommOn Y op)] [Algebra O R] [Algebra O (heckeAlg Y op)]
    (f : R →ₐ[O] heckeAlg Y op) (lam : A → R) (hl : ∀ b, f (lam b) = algebraMap A _ b) :
    ∃ μ : R →+* Module.End A Y, (∀ t, μ t = (f t : Module.End A Y)) ∧ ∀ b y, μ (lam b) y = b • y := by
  refine ⟨(heckeAlg Y op).val.toRingHom.comp f.toRingHom, fun _ => rfl, fun b y => ?_⟩
  change (f (lam b) : Module.End A Y) y = _
  rw [hl]
  rfl
private theorem ae_nt {A P ι : Type} [CommRing A] [AddCommGroup P] [Module A P] {Y : Submodule A P}
    {op : ι → Module.End A P} [Nontrivial (heckeAlg Y op)] : ¬ Subsingleton Y := fun _ =>
  absurd (inferInstance : Subsingleton (heckeAlg Y op)) (not_subsingleton _)
private theorem ae_zero {A M N : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (h : Subsingleton M) (φ : M →ₗ[A] N) (s : Module.End A M) (t : Module.End A N) (y : M) : φ (s y) = t (φ y) := by
  rw [Subsingleton.elim y 0, map_zero, map_zero, map_zero]
end Helpers
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ)
  (a : H.Op → c.O) {R : Type} [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq)
  (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ)
private def ae_Ok (K : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) : Prop :=
  Subsingleton (H.MK θ a K) ∨
    ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K)) (f : R →ₐ[c.O] H.TK θ a K),
      H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K))
private theorem ae_ex (lam : A →ₐ[c.O] R) (K : H.Lev) (J : Ideal R) (hJ : H.IsJ θ a K D₀ ψ₀ lam J) :
    ∃ μ : R →+* Module.End A (H.MK θ a K), (∀ b y, μ (lam b) y = b • y) ∧ ae_Ok H θ a D₀ ψ₀ K μ := by
  rcases hJ with h | ⟨i1, i2, f, -, hf, -, hl, -⟩
  · exact (ae_bot (A := A) (R := R) (P := H.X.Fn A H.m) (Y := H.MK θ a K) h.1 lam).imp fun μ h => ⟨h.1, .inl h.2⟩
  · exact (ae_mu (A := A) (P := H.X.Fn A H.m) (Y := H.MK θ a K) (op := H.op A) f lam hl).imp
      fun μ h => ⟨h.2, .inr ⟨i1, i2, f, hf, h.1⟩⟩
private theorem ae_cmp (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hH : H.Ax) (hθ : H.IsWt θ)
    (hU : ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T),
      D₀.map f.toRingHom = D₀.map g.toRingHom →
      (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g)
    (K K' : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) (μ' : R →+* Module.End A (H.MK θ a K'))
    (h : ae_Ok H θ a D₀ ψ₀ K μ) (h' : ae_Ok H θ a D₀ ψ₀ K' μ') (φ : H.MK θ a K →ₗ[A] H.MK θ a K') (hφ : Function.Injective φ)
    (hc : ∀ i (y y' : H.MK θ a K), (y' : H.X.Fn A H.m) = H.op A i y → (φ y' : H.X.Fn A H.m) = H.op A i (φ y)) (t : R)
    (y : H.MK θ a K) : φ (μ t y) = μ' t (φ y) := by
  rcases h with h | ⟨i1, i2, f, hf, e⟩
  · exact ae_zero h φ (μ t) (μ' t) y
  rcases h' with h | ⟨i1', i2', f', hf', e'⟩
  · exact h.elim _ _
  rw [e, e']
  exact _root_.UpperTheory.V.Hi.level_change_compat_rank_two_of_dense_weight hN L Ω l n c H hH A θ hθ a K K' R D₀ ψ₀ hU f f' hf hf' φ hφ (fun i y => hc i y _ rfl) t y
private theorem ae_out (K : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) (h : ae_Ok H θ a D₀ ψ₀ K μ)
    [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)] :
    ∃ f : R →ₐ[c.O] H.TK θ a K, H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K)) := by
  rcases h with h | ⟨_, _, h⟩
  · exact absurd h (ae_nt (op := H.op A))
  · exact h
private theorem ae_op (hH : H.Ax) (q : H.Q) (g : GLw n (H.wq q)) (i : H.Op) :
    Commute (H.X.ra (H.τA A) (H.sec (H.wq q) g)) (H.op A i) := by
  rcases i with x | x
  · exact ae_dc _ _ _ (hH.sectionsCommuteAtSplit q _ x.1.2 g) _ _ _
  · exact ae_commU _ _ _ _
end
theorem UpperTheory.V.Hi.levelUR2ActEx_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) [DecidableEq H.Q] (ρ : Representation A (GV n H.wq) (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (∀ q g f, (ρ (Pi.mulSingle q g) f : H.X.Fn A H.m) = H.X.ra (H.τA A) (H.sec (H.wq q) g) f) → (∀ K : H.Lev, (fixd ρ (Subgroup.pi Set.univ K.1)).map (Submodule.subtype _) = H.MK θ a K) → (∀ f : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), ∃ K, (f : H.X.Fn A H.m) ∈ H.MK θ a K) → ∀ (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (lam : A →ₐ[c.O] R), (∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D₀.map f.toRingHom = D₀.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g) → (∀ K, ∃ J, H.IsJ θ a K D₀ ψ₀ lam J) → ∃ α : R →+* Module.End A (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), (∀ b z, α (lam b) z = b • z) ∧ (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧ ∀ (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∃ f : R →ₐ[c.O] H.TK θ a K, H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t (y : H.MK θ a K) (z : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (z : H.X.Fn A H.m) = y → (α t z : H.X.Fn A H.m) = ((f t : Module.End A (H.MK θ a K)) y : H.MK θ a K) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ a _ ρ hρ hfix hex R _ _ D₀ ψ₀ lam hU hJ
  haveI : Nonempty H.Lev := ⟨⟨fun q => KO _ (Fin n), fun q => ⟨GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩⟩⟩
  choose μ hμ1 hμ2 using fun K => ae_ex H θ a D₀ ψ₀ lam K _ (hJ K).choose_spec
  obtain ⟨α, h1, h2⟩ := ae_abs (H.MK θ a) _ (H.op A) ρ (fun K : H.Lev => Subgroup.pi Set.univ K.1) hfix hex ae_inf ae_conj
    (ae_gen _ (H.op A) ρ (fun q g => H.X.ra (H.τA A) (H.sec (H.wq q) g)) hρ (ae_op H hH)) μ
    (fun K K' => ae_cmp H θ a D₀ ψ₀ hN hH hθ hU K K' _ _ (hμ2 K) (hμ2 K'))
  refine ⟨α, fun b z => ?_, h1, fun K i1 i2 => ?_⟩
  · obtain ⟨K, hK⟩ := hex z
    exact Subtype.ext ((h2 K _ ⟨z, hK⟩ z rfl).trans (congrArg Subtype.val (hμ1 K b ⟨z, hK⟩)))
  · obtain ⟨f, hf, e⟩ := ae_out H θ a D₀ ψ₀ K _ (hμ2 K)
    refine ⟨f, hf, fun t y z hz => ?_⟩
    rw [← e]
    exact h2 K t y z hz
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SphUntw
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.W
def TwAwayAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ)
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (R : G K Ω →* GL (Fin n) (Qbar l)), Continuous R →
    ∀ (art : Ideles K →* Gab K Ω) (κ : HChar K) (m : (K →+* ℂ) → ℤ) (μ : G K Ω →* (Qbar l)ˣ), IsGlobalArtin art → Continuous μ →
    IsLAdicOf art ι κ m μ → ∀ (w : HeightOneSpectrum (𝓞 K)), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal →
    ∀ τ τ' : SmIrr (GL (Fin n) (w.adicCompletion K)), Good (IrrGL.of τ.ρ τ.smooth τ.irred) →
    Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion K) → WD h), IsRecT h rc →
      IsWDOf ι R (rc (algNorm τ)) → IsWDOf ι (tw R μ) (rc (algNorm τ'))
def SphUntwAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n : ℕ) (κ : HChar K)
    (w : HeightOneSpectrum (𝓞 K)) (τ τ' : SmIrr (GL (Fin n) (w.adicCompletion K))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w τ'.ρ B →
    Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) → Good (IrrGL.of τ.ρ τ.smooth τ.irred) ∧
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion K) → WD h), IsRecT h rc → Gd (rc (algNorm τ))
def PsFullAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ (τ : SmIrr (GL (Fin n) (w.adicCompletion L)))
    (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ) (hh : Fin n → (L →+* Qbar l) → ℤ) (ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ)
    (ph : Fin n → Ine (F := L) A →* (Qbar l)ˣ), IsSubquotient τ.ρ (Hi.PS ω) → (∀ i, Hi.OrdChar ι a (ω i) (hh i) (ψ i)) →
    (∀ j, V.W.IsWtPart h (ψ j) (fun e => hh j (e.1.comp (algebraMap L (w.adicCompletion L)))) (ph j)) → Function.Injective ph →
    Nonempty (τ.ρ.Equiv (Hi.PS ω))
end UpperTheory.V.Z.Desc.W
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymUse
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open UpperTheory.V.W (Plc Lp)
namespace UpperTheory.V.Z.Sym
structure AdInAlt {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (M m : ℕ) (r : G L Ω →* GL (Fin 2) (Qbar l)) : Prop where
  cont : Continuous r
  aut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r
  irr : IrrOpen r
  gap : 2 ≤ m
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, r s = 1
  away : ∃ τ : Fin 2 → G L Ω →* (Qbar l)ˣ, (∀ i, Continuous (τ i)) ∧ TypeAway r τ
  above : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
    ∃ (b : ℤ) (k : ℕ) (κ : Fin 2 → ↥(Dec (F := L) A) →* (Qbar l)ˣ), 0 < k ∧ IsFlagOn r (Dec (F := L) A) κ ∧
      ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
        κ 0 s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ 1 s ^ k = (cycBar L Ω l s ^ b) ^ k
def UnitaryThreeAutomorphyDense : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra K Ω] [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω) (N w : ℕ) (χ' η θ : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ),
    FieldPairCharacterTripleConditions K L c N w χ' η θ j → χ' ≠ η → ∀ M : ℕ, M ≠ 0 → 2 * l ∣ M → UnrSplit L M →
    (∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, χ' (galEmb ℚ L Ω s) = 1) →
    ∀ B : ℕ, ∃ m ≥ B, m ≡ j [MOD l - 1] ∧ ∃ r : G L Ω →* GL (Fin 3) (Qbar l), IrrOpen r ∧
      _root_.UpperTheory.V.Sd.IsSeedAlt ι c (fun i => (![cycBar ℚ Ω l ^ j * χ', 1, (cycBar ℚ Ω l ^ j * χ')⁻¹] i).comp (galEmb ℚ L Ω))
        (fun i => (![χ', 1, χ'⁻¹] i).comp (galEmb ℚ L Ω)) ![(m : ℤ), 0, -(m : ℤ)] (cycBar L Ω l)⁻¹ r
end UpperTheory.V.Z.Sym
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp
private theorem ad_eq {H K : Type} [Group H] [CommRing K] {n : ℕ} (ρ : H →* GL (Fin n) K) (g : H) (X : Matrix (Fin n) (Fin n) K) :
    Loc.adGL ρ g X = W.mat ρ g * X * W.mat ρ g⁻¹ := by
  change _ = (ρ g : Matrix (Fin n) (Fin n) K) * X * (ρ g⁻¹ : GL (Fin n) K)
  rw [map_inv]
  rfl
private theorem cont_sub {H K : Type} [Group H] [TopologicalSpace H] [ContinuousInv H] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {n : ℕ} {a y : H → Matrix (Fin n) (Fin n) K} (ha : Continuous a) (hy : Continuous y)
    (X : Matrix (Fin n) (Fin n) K) : Continuous fun g => y g - (a g * X * a g⁻¹ - X) :=
  hy.sub (((ha.matrix_mul continuous_const).matrix_mul (ha.comp continuous_inv)).sub continuous_const)
theorem UpperTheory.V.Th.core_of_ord_vanishing_two_phi_all :
    _root_.UpperTheory.V.Th.OrdVan2Alt → W.PhiAll → _root_.UpperTheory.V.Th.DenseThresholdMainCase := by
  intro hO hΦ l _ L Ω _ _ _ _ _ _ s V hV _ c _ n h2 h4 r h0 B ι x ρ hN P R hP hR z hz hzo
  obtain ⟨h, hh⟩ := hN.arith
  obtain ⟨hD, -⟩ := Det.redB x ρ hN.rep
  have hfull : Submodule.span (Qbar l) (Set.range (W.mat ρ)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hs => hN.irr N fun g _ => hs g
  have hI := (Ws.Eb.relKill B x ρ hfull hD).2
  obtain ⟨X₀, hpol, hext⟩ := Det.polNorm V.frame ρ P R z hR hz.2
  have heps : ∃ g : V.frame.G₀, V.frame.ε g ≠ 1 := by
    obtain ⟨g, -, hg⟩ := h0.2.2
    refine ⟨g, fun e => hg ?_⟩
    have e' : (V.frame.ε.comp V.frame.η.ker.subtype) g = 1 := e
    rw [W.GFrame.eps, MonoidHom.comp_apply, e', map_one]
  have hdet := regDet V.frame c.O ρ P (by omega) (hΦ l L Ω s V).2.1 heps hN.cont hN.irr hN.n3
  have hno : ∀ (v : W.Vl l L) i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype := by
    intro v i j e
    by_cases hij : i = j
    · subst hij
      have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
      exact Det.epsDec (l := l) (L := L) (Ω := Ω) (s.A v.1) (s.w v.1) (s.hw v.1) ((s.hw v.1 ((l : ℕ) : 𝓞 L)).1 (by simpa only [map_natCast] using h1)) (left_eq_mul.1 e)
    · obtain ⟨g, hg, hf⟩ := hN.free v
      refine hf i j hij 1 one_pos ?_
      have e1 : V.ε (toGS Ω V.S' (W.resP L Ω (Subtype.val g))) = cycZ (W.Lp L) Ω l (W.resP L Ω (Subtype.val g)) :=
        DFunLike.congr_fun V.hε _
      have e2 : cycZ L Ω l (Subtype.val g) = 1 := e1.symm.trans hg
      have e3 : cycBar L Ω l (Subtype.val g) = 1 := by rw [cycBar, MonoidHom.comp_apply, e2, map_one]
      have e4 : x.psi v i g = x.psi v j g * cycBar L Ω l (Subtype.val g) := DFunLike.congr_fun e g
      rw [e3, mul_one] at e4
      simp only [pow_one]
      exact e4
  have hc : Continuous fun g : V.frame.G₀ => W.mat ρ g := Units.continuous_val.comp hN.cont
  refine (hO l L Ω s V c n r B ι x h ρ P hV h2 h4 h0 hh hD hN.cont hN.aut hfull hP hN.unr0 hno hdet
    (fun g => z g - Pa.dY V.frame (W.mat ρ) X₀ g) ⟨?_, fun g g' => ?_, hpol, fun u g hg => ?_, fun v => ?_⟩).elim hext
  · exact cont_sub hc (hz.1.comp continuous_subtype_val) X₀
  · have e1 : z ((g * g' : V.frame.G₀) : V.frame.Γ) = z g + W.mat ρ g * z g' * W.mat ρ g⁻¹ := by
      rw [← ad_eq, ← hR.ad]
      exact hz.2 _ _
    have e2 : W.mat ρ g * W.mat ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    simp only [e1, Pa.dY, _root_.mul_inv_rev, map_mul]
    noncomm_ring
  · simp only [hzo.ine u g hg, Pa.dY, W.mat, MonoidHom.comp_apply, map_inv, hI u g hg]
    simp
  · obtain ⟨a, X, ha⟩ := hzo.ord v
    refine ⟨a⁻¹, X - X₀, fun g => ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := ha g
    have e : z (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) X₀ (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) (X - X₀) (V.frame.φ v g) =
        z (V.frame.φ v g) - (Loc.adGL (ρ.comp (V.frame.φ v)) g X - X) := by
      rw [ad_eq]
      have e1 : ∀ t, W.mat (ρ.comp (V.frame.φ v)) t = W.mat ρ (V.frame.φ v t) := fun _ => rfl
      simp only [Pa.dY, e1, map_inv]
      noncomm_ring
    rw [inv_inv, e]
    exact ⟨a1, a2, a3, a4⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNiceSmall
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp
private theorem charpoly_flag' {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) : (Pr.gm r s).charpoly = Pr.chPoly κ s := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (Pr.gm r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]
theorem UpperTheory.V.Th.nice_zero_of_rank_two_or_three_irreducible_free :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r} (ι : Qbar l ≃+* ℂ) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), (n = 2 ∨ n = 3) → _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ → U3.MatIrr ⊤ (W.mat ρ) → Th.Free V.frame (fun v => x.psi v) → (∃ v a b g, r.psib v a g ≠ r.psib v b g) → _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x ρ := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B ι x ρ hn hA hirr hfree ⟨v, hne⟩
  have hp : n.Prime := by
    rcases hn with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  have h3 : n ≤ 3 := by omega
  obtain ⟨-, A, _, j, φ, hj, hred, hlift⟩ := Th.Det.redB x ρ hA.rep
  haveI : V.frame.G'.Normal := MonoidHom.normal_ker _
  haveI : CompactSpace V.frame.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ V.frame.η_open).isCompact
  have key := Th.Det.irrSmall hp V.frame.G' ρ j φ r.chib (V.frame.φ v) (x.psi v) (r.psib v) hirr hj hred
    (hA.flag v) (hlift v) (hfree v) hne
  refine ⟨hA, hfree, ?_, ?_⟩
  · have h := key ⊤ (by simp)
    rwa [top_inf_eq] at h
  · obtain ⟨g, hg, hfr⟩ := hfree v
    exact Th.Det.n3small h3 V.frame.G' ρ hA.cont key
      ⟨V.frame.φ v g, hg, fun i => x.psi v i g, hfr, charpoly_flag' _ _ (hA.flag v) g⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSpanEig
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
theorem UpperTheory.V.Z.Sym.Al.exists_eigenvector_in_span_of_comp_eq_trivial :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π →
        ∀ w : Plc L, IsSplitAt w → ∀ (W : Sig.Lev (Kw w)) ψ, CompEq π w ψ → (∀ i, ∀ u ∈ W.H, ψ i u = 1) →
        ∀ φ : UA L n → V, φ ≠ 0 → CoefIn φ π →
        ∃ φ', φ' ≠ 0 ∧ InSpan w φ φ' ∧ (∀ x ∈ locU n w, cLoc w x ∈ W.J n → ∀ g, φ' (g * x) = φ' g) ∧ EigT φ' w W ψ := by
  intro hLit L _ _ _ n V _ _ _ π hπ w hw W ψ ⟨hsm, τ, hτ, ⟨e⟩⟩ hψ φ hφ hc
  obtain ⟨s1, -, s3, -⟩ := secSpec L n w hw
  let N : Submodule ℂ (UA L n → V) := Submodule.span ℂ {ψ' | ∃ x ∈ locU n w, ψ' = fun g => φ (g * x)}
  let ρ : Representation ℂ (GL (Fin n) (Kw w)) (UA L n → V) := (rightReg ℂ (UA L n) V).comp (secW n w)
  have hρ : ∀ h (a : UA L n → V) g, ρ h a g = a (g * secW n w h) := fun _ _ _ => rfl
  have hst : ∀ h, ∀ a ∈ N, ρ h a ∈ N := by
    intro h a ha
    refine Submodule.span_induction (p := fun a _ => ρ h a ∈ N) ?_ (by simp) (fun _ _ _ _ h1 h2 => by
      rw [map_add (f := _)]; exact N.add_mem h1 h2) (fun c _ _ h1 => by rw [map_smul]; exact N.smul_mem c h1) ha
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.subset_span ⟨secW n w h * x, (locU n w).mul_mem (s1 h) hx, ?_⟩
    funext g
    rw [hρ, mul_assoc]
  let ν : Representation ℂ (GL (Fin n) (Kw w)) N :=
    { toFun := fun h => (ρ h).restrict (hst h)
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hν : ∀ h (a : N), ((ν h a : N) : UA L n → V) = ρ h a := fun _ _ => rfl
  have hφN : φ ∈ N := Submodule.subset_span ⟨1, (locU n w).one_mem, by funext g; rw [mul_one]⟩
  have hco : ∀ a : N, CoefIn (a : UA L n → V) π := fun a =>
    (spanKeep L n V w φ a a.2).1 π hπ hc
  let b := Module.finBasis ℂ V
  let q : Fin (Module.finrank ℂ V) → N →ₗ[ℂ] π := fun i =>
    { toFun := fun a => ⟨b.coord i ∘ (a : UA L n → V), hco a _⟩
      map_add' := fun x y => Subtype.ext (by funext g; simp)
      map_smul' := fun c x => Subtype.ext (by funext g; simp) }
  haveI : Nontrivial N := ⟨⟨⟨φ, hφN⟩, 0, fun h => hφ (congrArg Subtype.val h)⟩⟩
  obtain ⟨f, hf0, hf⟩ := (isoCopy _ _ _ τ.ρ ((repOn hπ).comp (secW n w)) τ.irred
    (isoTypic L n π hπ w hw τ hτ)).2 N (Fin (Module.finrank ℂ V)) ν q
      (fun i h x => Subtype.ext rfl)
      (fun x hx => Subtype.ext (by
        funext g
        refine b.ext_elem fun i => ?_
        have : b.repr ((x : UA L n → V) g) i = 0 := congrFun (congrArg Subtype.val (hx i)) g
        simpa using this)) inferInstance
  have hinj : Function.Injective f := by
    haveI := τ.irred
    let Φ : τ.ρ.IntertwiningMap ν :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := f.map_smul
        isIntertwining' := fun g => LinearMap.ext fun x => hf g x }
    refine (Representation.IsIrreducible.injective_or_eq_zero Φ).resolve_right fun h => hf0 ?_
    exact LinearMap.ext fun x => congrArg (fun Ψ : τ.ρ.IntertwiningMap ν => Ψ x) h
  obtain ⟨v, hv0, hvJ, hvE⟩ := _root_.UpperTheory.V.Z.Sym.Al.exists_fixd_dc_eq_expo_smul_of_equiv_prinSeries hLit (Kw w) n W ψ hsm hψ τ.V τ.ρ ⟨e⟩
  refine ⟨f v, fun h => hv0 (hinj (Subtype.ext (by simpa using h))), (f v).2, ?_, ?_⟩
  · intro x hx hJ g
    have h1 := hf (cLoc w x) v
    rw [hvJ _ hJ] at h1
    have h2 := congrFun (congrArg Subtype.val h1) g
    rw [hν, hρ, s3 x hx] at h2
    exact h2.symm
  · intro d hd
    have h1 := dcMap W τ.ρ ρ (N.subtype ∘ₗ f) (fun h x => by simp [hf, hν]) (Sig.dg d) v
    rw [hvE d hd] at h1
    simpa [EigAt, ρ] using h1.symm
end
end

