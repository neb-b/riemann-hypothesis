module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0007
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0045

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartAdd
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem chart_add_coeff {K τ τ' : Type} [CommRing K] (ε : τ ≃ τ') (p : MvPowerSeries τ K) (n : τ' →₀ ℕ) :
    coeff n (rename ε p) = coeff (Finsupp.mapDomain ε.symm n) p := by
  have h := coeff_embDomain_rename ε.toEmbedding p (Finsupp.mapDomain ε.symm n)
  rw [Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp] at h
  have h2 : (ε.toEmbedding : τ → τ') ∘ ε.symm = id := funext fun x => ε.apply_symm_apply x
  rw [h2, Finsupp.mapDomain_id] at h
  exact h

private theorem chart_add_weight {τ τ' X : Type} [AddCommGroup X] (g : τ' → τ) (wt : τ → X) (n : τ' →₀ ℕ) :
    Finsupp.weight wt (Finsupp.mapDomain g n) = Finsupp.weight (fun s => wt (g s)) n := by
  induction n using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), ha, hb]
  | single a b => simp [Finsupp.weight_single]

private theorem chart_add_rename {O A X τ τ' : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    [AddCommGroup X] {𝒜 : X → Submodule O A} {x : A →ₐ[O] O} {wt : τ → X}
    {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)} (h : IsChart 𝒜 x wt φ) (ε : τ ≃ τ') (wt' : τ' → X)
    (hw : ∀ s, wt' s = wt (ε.symm s)) :
    IsChart 𝒜 x wt' (((rename ε).restrictScalars O).comp φ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j f hf n hn
    show coeff n (rename ε (φ f)) = 0
    rw [chart_add_coeff]
    refine h.graded j f hf _ ?_
    rwa [chart_add_weight, ← funext hw]
  · intro f
    show constantCoeff (rename ε (φ f)) = _
    rw [constantCoeff_rename, h.const]
  · intro i
    obtain ⟨f, h1, h2⟩ := h.onto (ε.symm i)
    refine ⟨f, ?_, fun i' hi' => ?_⟩
    · show coeff _ (rename ε (φ f)) ≠ 0
      rwa [chart_add_coeff, Finsupp.mapDomain_single]
    · show coeff _ (rename ε (φ f)) = 0
      rw [chart_add_coeff, Finsupp.mapDomain_single]
      exact h2 _ fun h3 => hi' (ε.symm.injective h3)
  · intro f hx hf
    refine h.inj f hx fun i => ?_
    have h1 : coeff _ (rename ε (φ f)) = 0 := hf (ε i)
    rwa [chart_add_coeff, Finsupp.mapDomain_single, ε.symm_apply_apply] at h1

private def chart_add_equiv (F : Bool → Type) : (Σ v, F v) ≃ F true ⊕ F false where
  toFun
    | ⟨true, s⟩ => .inl s
    | ⟨false, s⟩ => .inr s
  invFun
    | .inl s => ⟨true, s⟩
    | .inr s => ⟨false, s⟩
  left_inv
    | ⟨true, _⟩ => rfl
    | ⟨false, _⟩ => rfl
  right_inv
    | .inl _ => rfl
    | .inr _ => rfl

private def chart_add_fam (A B : Type) : Bool → Type := fun v => Bool.rec B A v

theorem UpperTheory.V.Alg.chart_add :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) (τ : Type) [Fintype τ] (wt : τ → X) (φ : R →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart W.part (W.origin h) wt φ →
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] (W' : WPres O X R') (τ' : Type) [Fintype τ'] (e : W.σ ⊕ τ' ≃ W'.σ), (∀ s, W'.wt (e (.inl s)) = W.wt s) →
      RingHom.ker W'.π = (RingHom.ker W.π).map (MvPowerSeries.rename fun s => e (.inl s)) →
      ∃ (h' : W'.HasOrigin) (ψ : R' →ₐ[O] MvPowerSeries (τ ⊕ τ') (FractionRing O)), IsChart W'.part (W'.origin h') (Sum.elim wt fun s => W'.wt (e (.inr s))) ψ ∧
        (∀ s, ψ (W'.z (e (.inl s))) = MvPowerSeries.rename Sum.inl (φ (W.z s))) ∧ ∀ s, ψ (W'.z (e (.inr s))) = MvPowerSeries.X (.inr s) := by
  intro O X R _ _ _ _ iR aR W h τ fτ wt φ hφ R' _ _ W' τ' fτ' e hwt hker
  let W0 : WPres O X (MvPowerSeries τ' O) := WPres.free O fun s : τ' => W'.wt (e (.inr s))
  have h0 : W0.HasOrigin := fun f hf => by
    have : f = 0 := hf
    rw [this, map_zero]
  obtain ⟨φ0, hφ0, hz0⟩ := chart_free O X (MvPowerSeries τ' O) W0 h0 Function.injective_id
  let B : Bool → Type := chart_add_fam R (MvPowerSeries τ' O)
  letI iB : ∀ v : Bool, CommRing (B v) := fun v =>
    Bool.rec (motive := fun v : Bool => CommRing (B v)) (inferInstance : CommRing (MvPowerSeries τ' O)) iR v
  letI aB : ∀ v : Bool, Algebra O (B v) := fun v =>
    Bool.rec (motive := fun v : Bool => @Algebra O (B v) _ (iB v).toCommSemiring.toSemiring) (inferInstance : Algebra O (MvPowerSeries τ' O)) aR v
  let WB : ∀ v : Bool, WPres O X (B v) := fun v => Bool.rec (motive := fun v : Bool => WPres O X (B v)) W0 W v
  have hB : ∀ v : Bool, (WB v).HasOrigin := fun v => Bool.rec (motive := fun v : Bool => (WB v).HasOrigin) h0 h v
  let F : Bool → Type := chart_add_fam τ τ'
  letI fF : ∀ v : Bool, Fintype (F v) := fun v => Bool.rec (motive := fun v : Bool => Fintype (F v)) fτ' fτ v
  let wF : ∀ v : Bool, F v → X := fun v => Bool.rec (motive := fun v : Bool => F v → X) W0.wt wt v
  let φF : ∀ v : Bool, B v →ₐ[O] MvPowerSeries (F v) (FractionRing O) := fun v =>
    Bool.rec (motive := fun v : Bool => B v →ₐ[O] MvPowerSeries (F v) (FractionRing O)) φ0 φ v
  have hF : ∀ v : Bool, IsChart (WB v).part ((WB v).origin (hB v)) (wF v) (φF v) := fun v =>
    Bool.rec (motive := fun v : Bool => IsChart (WB v).part ((WB v).origin (hB v)) (wF v) (φF v)) hφ0 hφ v
  let e' : (Σ v, (WB v).σ) ≃ W'.σ := (chart_add_equiv fun v => (WB v).σ).trans e
  obtain ⟨h', ψ, hψ, hz⟩ := chart_sum O X Bool B WB hB F wF φF hF R' W' e'
    (fun v => Bool.rec (motive := fun v : Bool => ∀ s, W'.wt (e' ⟨v, s⟩) = (WB v).wt s) (fun _ => rfl) hwt v) (by
      rw [iSup_bool_eq, hker]
      have h1 : RingHom.ker (WB false).π = ⊥ := (RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id
      rw [h1, Ideal.map_bot, sup_bot_eq]
      rfl)
  let ε : (Σ v, F v) ≃ τ ⊕ τ' := chart_add_equiv F
  refine ⟨h', ((rename ε).restrictScalars O).comp ψ, chart_add_rename hψ ε _ ?_, fun s => ?_, fun s => ?_⟩
  · rintro (s | s) <;> rfl
  · have h1 := congrArg (rename ε) (hz true s)
    rw [rename_rename] at h1
    exact h1
  · have h1 := congrArg (rename ε) (hz false s)
    rw [rename_rename] at h1
    refine h1.trans ?_
    have h2 : φF false ((WB false).z s) = MvPowerSeries.X s := hz0 s
    rw [h2]
    exact rename_X _ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartGr
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private lemma lin_coeff_sq {O R K τ : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing K] [Algebra O K]
    (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries τ K)
    (hc : ∀ f, constantCoeff (φ f) = algebraMap O K (x f)) (i : τ) :
    ∀ g ∈ RingHom.ker x ^ 2, coeff (Finsupp.single i 1) (φ g) = 0 := by
  intro g hg
  rw [pow_two] at hg
  have hone : ∀ a ∈ RingHom.ker x, 1 ≤ (φ a).order := by
    intro a ha
    have hxa : x a = 0 := ha
    exact MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (by rw [hc, hxa, map_zero])
  have hord : ((2 : ℕ) : ℕ∞) ≤ (φ g).order := by
    refine Submodule.mul_induction_on (C := fun g => ((2 : ℕ) : ℕ∞) ≤ (φ g).order) hg ?_ ?_
    · intro a ha b hb
      rw [map_mul]
      calc ((2 : ℕ) : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ (φ a).order + (φ b).order := add_le_add (hone a ha) (hone b hb)
        _ ≤ (φ a * φ b).order := MvPowerSeries.le_order_mul
    · intro a b ha hb
      rw [map_add (f := _)]
      exact le_trans (le_min ha hb) MvPowerSeries.min_order_le_add
  apply MvPowerSeries.coeff_of_lt_order
  rw [Finsupp.degree_single]
  exact lt_of_lt_of_le (by norm_num) hord

theorem UpperTheory.V.Alg.chart_gr :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) [Module.Free ℤ X] [Module.Finite ℤ X] (τ : Type) (wt : τ → X) (φ : R →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart W.part (W.origin h) wt φ → IsChart W.gr (W.originA h) wt (φ.comp W.A.val) := by
  intro O X R _ _ _ _ _ _ W h _ _ τ wt φ hφ
  obtain ⟨hk, hsurj⟩ := ker_pow O R X W h 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j f hf
    exact hφ.graded j f.val hf
  · intro f
    exact hφ.const f.val
  · intro i
    obtain ⟨g, hg1, hg2⟩ := hφ.onto i
    obtain ⟨y, hy⟩ := hsurj g
    have hd : ∀ i', coeff (Finsupp.single i' 1) (φ (g - y)) = 0 :=
      fun i' => lin_coeff_sq (W.origin h) φ hφ.const i' _ hy
    have he : ∀ i', coeff (Finsupp.single i' 1) ((φ.comp W.A.val) y) =
        coeff (Finsupp.single i' 1) (φ g) := by
      intro i'
      have := hd i'
      rw [map_sub, map_sub, sub_eq_zero] at this
      exact this.symm
    refine ⟨y, ?_, ?_⟩
    · rw [he]
      exact hg1
    · intro i' hi'
      rw [he]
      exact hg2 i' hi'
  · intro f hf hco
    obtain ⟨c, hc0, hcf⟩ := hφ.inj f.val hf hco
    refine ⟨c, hc0, ?_⟩
    rw [← hk, Ideal.mem_comap]
    exact hcf
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Coprod
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem coprod_rename_mem {O : Type} [CommRing O] {X : Type} [AddCommGroup X] {σ τ : Type} [Finite σ]
    (u : σ → τ) (wt : τ → X) (ws : σ → X) (h : ∀ s, wt (u s) = ws s) {j : X} {g : MvPowerSeries σ O}
    (hg : g ∈ wtPart O ws j) : rename u g ∈ wtPart O wt j := fun n hn => by
  rw [coeff_rename]
  refine Finset.sum_eq_zero fun d hd => hg d fun hj => hn ?_
  have hd' : Finsupp.mapDomain u d = n := by simpa using hd
  rw [← hd', ← hj, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by rw [add_smul])]
  simp [h]

private theorem coprod_homog {O : Type} [CommRing O] {X : Type} [AddCommGroup X] {σ : Type} [Fintype σ]
    (wt : σ → X) {κ : Type} [Finite κ] (g : κ → MvPowerSeries σ O) (c : κ → X)
    (hg : ∀ i, g i ∈ wtPart O wt (c i)) : IsHomog O wt (Ideal.span (Set.range g)) := by
  have hp : ∀ i, g i ∈ (WPres.free O wt).part (c i) := fun i => ⟨g i, hg i, rfl⟩
  exact (homog_span O _ X (WPres.free O wt) κ (fun i => ⟨g i, (WPres.free O wt).part_le_A (hp i)⟩) c hp).1

private theorem coprod_ext {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] {σ : Type} [Finite σ]
    (F G : MvPowerSeries σ O →ₐ[O] R') (hF : ∀ s, F (X s) ∈ maximalIdeal R') (h : ∀ s, G (X s) = F (X s)) :
    G = F :=
  (co_ev O O R' σ (Algebra.ofId O R') _ hF).unique ⟨fun x => G.commutes x, h⟩
    ⟨fun x => F.commutes x, fun _ => rfl⟩

theorem UpperTheory.V.Alg.coprod :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] (T : Type) [Fintype T] (B : T → Type) [∀ v, CommRing (B v)] [∀ v, Algebra O (B v)] [∀ v, IsCO O (B v)] (WB : ∀ v, WPres O X (B v)), (∀ v s, (WB v).z s ∈ maximalIdeal (B v)) →
      ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (i : ∀ v, B v →ₐ[O] R) (W : WPres O X R) (e : (Σ v, (WB v).σ) ≃ W.σ),
        (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : ∀ v, B v →ₐ[O] R'), ∃! F : R →ₐ[O] R', ∀ v, F.comp (i v) = f v) ∧
        (∀ v s, W.wt (e ⟨v, s⟩) = (WB v).wt s ∧ W.z (e ⟨v, s⟩) = i v ((WB v).z s)) ∧ (∀ v j, ∀ x ∈ (WB v).part j, i v x ∈ W.part j) ∧
        RingHom.ker W.π = ⨆ v, (RingHom.ker (WB v).π).map (MvPowerSeries.rename fun s => e ⟨v, s⟩) := by
  intro O _ _ _ _ X _ T _ B _ _ _ WB hz
  classical
  let σ : Type := Σ v, (WB v).σ
  let wt : σ → X := fun p => (WB p.1).wt p.2
  let r : ∀ v, MvPowerSeries (WB v).σ O →ₐ[O] MvPowerSeries σ O :=
    fun v => rename fun s => (⟨v, s⟩ : σ)
  have hr : ∀ v j g, g ∈ wtPart O (WB v).wt j → r v g ∈ wtPart O wt j :=
    fun v j g hg => coprod_rename_mem _ wt _ (fun _ => rfl) hg
  have hrX : ∀ v s, r v (MvPowerSeries.X s) = MvPowerSeries.X ⟨v, s⟩ := fun v s => rename_X _ s
  let J : Ideal (MvPowerSeries σ O) := ⨆ v, (RingHom.ker (WB v).π).map (r v)
  have hJ : ∀ v g, (WB v).π g = 0 → r v g ∈ J := fun v g hg =>
    le_iSup (fun v => (RingHom.ker (WB v).π).map (r v)) v (Ideal.mem_map_of_mem _ hg)
  have hJm : J ≤ maximalIdeal _ := iSup_le fun v => Ideal.map_le_iff_le_comap.2 fun g hg hu => by
    have h1 : IsUnit g := by
      have h2 := isUnit_constantCoeff _ hu
      rw [isUnit_iff_constantCoeff]
      rwa [show constantCoeff (r v g) = constantCoeff g from constantCoeff_rename _ g] at h2
    have h3 := h1.map (WB v).π
    rw [show (WB v).π g = 0 from hg] at h3
    exact not_isUnit_zero h3
  have hJh : IsHomog O wt J := by
    choose n g c hg hs using fun v => ker_gen O X (WB v).σ (WB v).wt _ (WB v).homog
    have : J = Ideal.span (Set.range fun p : Σ v, Fin (n v) => r p.1 (g p.1 p.2)) := by
      rw [Set.range_sigma_eq_iUnion_range, Ideal.span_iUnion]
      refine iSup_congr fun v => ?_
      rw [hs v, Ideal.map_span, ← Set.range_comp]
      rfl
    rw [this]
    exact coprod_homog wt _ (fun p => c p.1 p.2) fun p => hr _ _ _ (hg p.1 p.2)
  haveI : IsCO O (MvPowerSeries σ O) := co_mvps O O σ
  haveI : Nontrivial (MvPowerSeries σ O ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hJm)
  let π := Ideal.Quotient.mkₐ O J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective O J
  have hk : RingHom.ker π = J := Ideal.Quotient.mkₐ_ker O J
  haveI hR : IsCO O (MvPowerSeries σ O ⧸ J) := co_quot O (MvPowerSeries σ O) _ π hπ
  let i : ∀ v, B v →ₐ[O] MvPowerSeries σ O ⧸ J := fun v =>
    (Ideal.Quotient.liftₐ (RingHom.ker (WB v).π) (π.comp (r v)) fun g hg =>
      Ideal.Quotient.eq_zero_iff_mem.2 (hJ v g hg)).comp
      (Ideal.quotientKerAlgEquivOfSurjective (WB v).surj).symm.toAlgHom
  have hi : ∀ v g, i v ((WB v).π g) = π (r v g) := fun v g => by
    have : (Ideal.quotientKerAlgEquivOfSurjective (WB v).surj).symm ((WB v).π g) = Ideal.Quotient.mk _ g := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    simp only [i, AlgHom.comp_apply, AlgEquiv.coe_algHom]
    erw [this]
    rfl
  refine ⟨_, inferInstance, inferInstance, hR, i, ⟨σ, wt, π, hπ, by rw [hk]; exact hJh⟩, Equiv.refl _, ?_,
    fun v s => ⟨rfl, ?_⟩, ?_, hk⟩
  · intro R' _ _ _ f
    have ha : ∀ v s, f v ((WB v).z s) ∈ maximalIdeal R' := fun v s => by
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hz v s
    obtain ⟨F, ⟨-, hF⟩, -⟩ := co_ev O O R' σ (Algebra.ofId O R') (fun p => f p.1 ((WB p.1).z p.2))
      fun p => ha p.1 p.2
    have hFr : ∀ v, F.comp (r v) = (f v).comp (WB v).π := fun v =>
      coprod_ext _ _ (ha v) fun s => by rw [AlgHom.comp_apply, hrX, hF]; rfl
    have hFJ : ∀ g ∈ J, F g = 0 := by
      have : J ≤ RingHom.ker F := iSup_le fun v => Ideal.map_le_iff_le_comap.2 fun g hg => by
        show F.comp (r v) g = 0
        rw [hFr, AlgHom.comp_apply, show (WB v).π g = 0 from hg, map_zero]
      exact this
    refine ⟨Ideal.Quotient.liftₐ J F hFJ, fun v => ?_, fun G hG => ?_⟩
    · ext x
      obtain ⟨g, rfl⟩ := (WB v).surj x
      rw [AlgHom.comp_apply, hi]
      exact DFunLike.congr_fun (hFr v) g
    · have : G.comp π = F := coprod_ext _ _ (fun p => by rw [hF]; exact ha _ _) fun p => by
        rw [hF, ← hG, AlgHom.comp_apply, AlgHom.comp_apply, WPres.z, hi, hrX]
      ext x
      obtain ⟨g, rfl⟩ := hπ x
      exact DFunLike.congr_fun this g
  · show π _ = i v ((WB v).π _)
    rw [hi, hrX]
    rfl
  · rintro v j _ ⟨g, hg, rfl⟩
    exact ⟨r v g, hr v j g hg, (hi v g).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerExtend
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

private theorem der_algebraMap {O A Q : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup Q]
    [Module O Q] (x : A →ₐ[O] O) (D : A →ₗ[O] Q) (hD : D ∈ PtDer x Q) (c : O) : D (algebraMap O A c) = 0 := by
  have h1 : D 1 = 0 := by
    have h : D (1 * 1) = x 1 • D 1 + x 1 • D 1 := hD 1 1
    rw [mul_one, map_one x, one_smul] at h
    simpa using h
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]

private theorem der_sq {O A Q : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup Q]
    [Module O Q] (x : A →ₐ[O] O) (D : A →ₗ[O] Q) (hD : D ∈ PtDer x Q) (f : A) (hf : f ∈ RingHom.ker x ^ 2) :
    D f = 0 := by
  rw [pow_two] at hf
  refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero])
  have h : D (a * b) = x a • D b + x b • D a := hD a b
  rw [h, (RingHom.mem_ker).1 ha, (RingHom.mem_ker).1 hb, zero_smul, zero_smul, add_zero]

theorem UpperTheory.V.Alg.der_extend :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (W : WPres O X R) (h : W.HasOrigin) (Q : Type) [AddCommGroup Q] [Module O Q],
      (∀ D ∈ PtDer (W.originA h) Q, ∃! D' : R →ₗ[O] Q, D' ∈ PtDer (W.origin h) Q ∧ D' ∘ₗ W.A.val.toLinearMap = D) ∧
      ∀ D ∈ PtDer (W.origin h) Q, (∀ s, D (W.z s) = 0) → D = 0 := by
  intro O R _ _ _ X _ _ _ _ W h Q _ _
  obtain ⟨hk, hy⟩ := UpperTheory.V.Alg.ker_pow O R X W h 2
  choose y hy using hy
  refine ⟨fun D hD => ?_, fun D hD hz => ?_⟩
  · have key : ∀ (x : R) (a : W.A), x - a ∈ RingHom.ker (W.origin h) ^ 2 → D (y x) = D a := fun x a ha => by
      rw [← sub_eq_zero, ← map_sub]
      refine der_sq _ D hD _ ?_
      rw [← hk, Ideal.mem_comap]
      have := sub_mem ha (hy x)
      convert this using 1
      simp
    have horig : ∀ x : R, W.origin h x = W.originA h (y x) := fun x => by
      have h1 : x - y x ∈ RingHom.ker (W.origin h) := Ideal.pow_le_self two_ne_zero (hy x)
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1
      exact h1
    let D' : R →ₗ[O] Q :=
      { toFun := fun x => D (y x)
        map_add' := fun a b => by
          rw [← map_add (f := _)]
          refine key _ _ ?_
          have := add_mem (hy a) (hy b)
          convert this using 1
          push_cast
          ring
        map_smul' := fun c a => by
          rw [RingHom.id_apply, ← map_smul]
          refine key _ _ ?_
          have := Submodule.smul_of_tower_mem _ c (hy a)
          convert this using 1
          rw [smul_sub]
          rfl }
    refine ⟨D', ⟨fun a b => ?_, ?_⟩, ?_⟩
    · have h1 : D (y a * y b) = W.originA h (y a) • D (y b) + W.originA h (y b) • D (y a) := hD _ _
      show D (y (a * b)) = W.origin h a • D (y b) + W.origin h b • D (y a)
      rw [horig a, horig b, ← h1]
      refine key _ _ ?_
      have := add_mem (Ideal.mul_mem_right b _ (hy a)) (Ideal.mul_mem_left _ (y a : R) (hy b))
      convert this using 1
      push_cast
      ring
    · ext a
      exact key _ a (by simp)
    · rintro E ⟨hE, rfl⟩
      ext x
      have := der_sq _ E hE _ (hy x)
      rw [map_sub, sub_eq_zero] at this
      exact this
  · ext x
    obtain ⟨f, rfl⟩ := W.surj x
    have hspan : ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : W.σ → MvPowerSeries W.σ O)),
        D (W.π g) = 0 := fun g hg => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hg
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      have h1 : D (W.π (c i) * W.z i) = W.origin h (W.π (c i)) • D (W.z i) + W.origin h (W.z i) • D (W.π (c i)) :=
        hD _ _
      have h2 : W.origin h (W.z i) = 0 := by
        rw [WPres.z, W.origin_π]
        simp
      rw [map_mul]
      rw [hz i, h2, smul_zero, zero_smul, add_zero] at h1
      exact h1
    have h1 := hspan (f - algebraMap O _ (constantCoeff f))
      (mem_span_X _ (by simp [MvPowerSeries.algebraMap_apply]))
    rw [map_sub, AlgHom.commutes, map_sub, der_algebraMap _ D hD, sub_zero] at h1
    exact h1
end

