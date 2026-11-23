module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X Y : Scheme.{0}} (L : LB X)

theorem exists_gen_prod (K : ℕ → Type) [∀ i, Fintype (K i)] (φ : ∀ i, K i → (Y ⟶ X)) (ε : ∀ i, K i → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) (n : ℕ) :
    ∃ (K' : Type) (_ : Fintype K') (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t' : LB.Gen (LB.LinComb L φ' ε')),
      t'.IsGen ∧
      (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U),
        ∏ k, h (φ' k) ^ ε' k = ∏ i ∈ Finset.range n, ∏ k, h (φ i k) ^ ε i k) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        val t' r z J = ∏ i ∈ Finset.range n, val (t i) r z J := by
  induction n with
  | zero =>
    refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L, ?_, ?_, ?_⟩
    · rintro (i : PEmpty.{1} → L.ι) (j : PEmpty.{1} → L.ι)
      have h0 : (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 :=
        rfl
      rw [h0, one_mul]
      simp only [LB.oneGen, map_one]
    · intro U _ h
      simp
    · intro Z r z J _
      simp [val, LB.oneGen]
      exact map_one (gm r z _)
  | succ n ih =>
    obtain ⟨K', hK', φ', ε', t', ht', hprod, hval⟩ := ih
    refine ⟨K' ⊕ K n, inferInstance, Sum.elim φ' (φ n), Sum.elim ε' (ε n),
      LB.mulGen L φ' ε' (φ n) (ε n) t' (t n),
      ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen L φ' ε' (φ n) (ε n) t' (t n) ht' (ht n), ?_, ?_⟩
    · intro U _ h
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_range_succ, hprod U h]
    · intro Z r z J hJ
      rw [val_mul, Finset.prod_range_succ, hval Z r z J hJ]
      exact hJ

theorem exists_const {S₀ : Scheme.{0}} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (hf : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) :
    ∃ a : Γ(S₀, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      (val t r z J).val = gs (r ≫ p) z ⊤ a := by
  classical
  have hcov : (⊤ : Y.Opens) ≤ ⨆ c : (Y ⟶ X) → L.ι, LB.wchart L φ (fun k => c (φ k)) := by
    intro y _
    have hc : ∀ ψ : Y ⟶ X, ∃ i, ψ.base y ∈ L.U i := by
      intro ψ
      have hy : ψ.base y ∈ (⨆ i, L.U i) := by rw [hL.cover]; simp
      exact TopologicalSpace.Opens.mem_iSup.1 hy
    choose c hc using hc
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, Set.mem_iInter.2 fun k => hc (φ k)⟩
  have hcompat : ∀ c c' : (Y ⟶ X) → L.ι,
      res (inf_le_left : LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)) ≤
        LB.wchart L φ (fun k => c (φ k))) (t.s (fun k => c (φ k))) =
      res (inf_le_right : LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)) ≤
        LB.wchart L φ (fun k => c' (φ k))) (t.s (fun k => c' (φ k))) := by
    intro c c'
    have hg := ht (fun k => c (φ k)) (fun k => c' (φ k))
    have h1 : (LB.LinComb L φ ε).g (fun k => c (φ k)) (fun k => c' (φ k)) = 1 := by
      refine Eq.trans ?_ (hf (Γ(Y, LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)))ˣ)
        (fun ψ => if hψ : ∃ k, φ k = ψ then
          res (show LB.wchart L φ (fun k => c (φ k)) ⊓ LB.wchart L φ (fun k => c' (φ k)) ≤
              ψ ⁻¹ᵁ (L.U (c ψ) ⊓ L.U (c' ψ)) by
            obtain ⟨k, rfl⟩ := hψ
            exact le_inf (inf_le_left.trans (LB.wchart_le L φ _ k))
              (inf_le_right.trans (LB.wchart_le L φ _ k)))
            (pullU ψ _ (L.g (c ψ) (c' ψ)))
          else 1))
      refine Finset.prod_congr rfl fun k _ => ?_
      show _ = (dite _ _ _) ^ ε k
      rw [dite_eq_left (show ∃ k', φ k' = φ k from ⟨k, rfl⟩)]
      rfl
    rw [h1, one_mul] at hg
    exact hg
  have key := TopCat.Sheaf.existsUnique_gluing' Y.sheaf
    (fun c : (Y ⟶ X) → L.ι => LB.wchart L φ (fun k => c (φ k))) ⊤ (fun _ => homOfLE le_top) hcov
  obtain ⟨f, hf1, -⟩ := key (fun c => (t.s (fun k => c (φ k))).val)
    (fun c c' => congrArg Units.val (hcompat c c'))
  obtain ⟨g, hg1, -⟩ := key (fun c => ((t.s (fun k => c (φ k)))⁻¹).val)
    (fun c c' => congrArg (fun u => (u⁻¹).val) (hcompat c c'))
  obtain ⟨e, -, he⟩ := key (fun _ => 1) (fun c c' => (map_one _).trans (map_one _).symm)
  have hfg : f * g = 1 :=
    (he (f * g) fun c => by rw [map_mul, hf1 c, hg1 c]; exact (t.s _).mul_inv).trans
      (he 1 fun c => map_one _).symm
  let fU : Γ(Y, ⊤)ˣ := Units.mkOfMulEqOne f g hfg
  obtain ⟨a, ha⟩ := hp fU.val
  refine ⟨a, fun Z r z J hJ => ?_⟩
  have hmem : r.base z ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => hJ (r ≫ φ k)
  have hres : res (le_top : LB.wchart L φ (fun k => J (r ≫ φ k)) ≤ ⊤) fU = t.s (fun k => J (r ≫ φ k)) :=
    Units.ext (hf1 (fun ψ => J (r ≫ ψ)))
  rw [val_of (t := t) (r := r) (z := z) (J := J) (j := fun k => J (r ≫ φ k)) (h := fun _ => rfl), ← hres,
    gm_res r z le_top hmem fU, ← gs_unit r z ⊤ (by simp) fU, ← ha]
  exact gs_pull r p z ⊤ (by simp) a

end ReciprocityTheory.ChartRestriction.G.H1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

def AlphaBarEnumStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso →
    letI := H.starRing
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F],
    ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a)
        (fun n g g' c => WeilIs P.A.A P.A.L n g g' (unitOn c))),
      ∃ (p : Fin (N ^ P.A.g) → QkPt P.D.toPre F (1 * N))
        (x : Fin (N ^ P.A.g) → (TFK (R := V) F ⟶ P.A.A)),
        (∀ b, P.ToA F (1 * N) (p b) (x b)) ∧ (∀ b, x b ≫ P.oA.act (star α) = 1) ∧
        Function.Injective x ∧
        ∀ y : TFK (R := V) F ⟶ P.A.A, y ≫ P.oA.act (star α) = 1 → ∃ b, x b = y

def CanonLiftFixStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso →
    letI := H.starRing
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F]
      (θ : Fam P.D.toPre F 1) (θα : Fam P.D.toPre F (1 * N)), PullAl P.D F P.oD α 1 N θ θα →
    ∀ (p : QkPt P.D.toPre F (1 * N)) (x : TFK (R := V) F ⟶ P.A.A), P.ToA F (1 * N) p x →
      x ≫ P.oA.act α = 1 →
      ∃ w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (1 * N))),
        w.IsGen ∧ FinOrd P.D F (1 * N) p w 1 ∧ PhiRel P.D.toPre F (1 * N) p w θα θα

def AlphaPairStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso →
    letI := H.starRing
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F],
    ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a)
        (fun n g g' c => WeilIs P.A.A P.A.L n g g' (unitOn c))),
    ∀ (x x' : TFK (R := V) F ⟶ P.A.A), x ≫ P.oA.act (star α) = 1 → x' ≫ P.oA.act (star α) = 1 → x ≠ x' →
      ∃ z : TFK (R := V) F ⟶ P.A.A, z ≫ P.oA.act α = 1 ∧
        ∃ c c' : Γ((TFK (R := V) F).left, ⊤)ˣ,
          WeilIs P.A.A P.A.L N z x c ∧ WeilIs P.A.A P.A.L N z x' c' ∧ c ≠ c'

def DimSplitStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t),
    P.A.g = Module.finrank ℤ P.D.toPre.X + P.D.toPre.P.g

def QkActExistsStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t),
    letI := H.starRing
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ) (a : 𝓞 E)
      (p : QkPt P.D.toPre F k), ∃ p' : QkPt P.D.toPre F k, QkAct P.oD a p p'

def DvrLevelFrame : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O),
      TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N : ℕ), 1 ≤ N → a * star a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)), PullAl D F oa a k N s s' →
      ∀ (χ : D.toPre.X) (σ : D.toPre.SecB k χ)
        (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))) (c : F),
        GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) σF
          (D.toPre.famφB χ) (DegPre.famε k) σ (DegPre.prB D.toPre F).left 1 →
        (∀ j, (s.s χ).f j = DegPre.constBF D.toPre F c _ * σF.f j) →
        (¬ ∃ σ' : D.toPre.SecB k χ, ∀ j, σ.f j = constFn D.toPre.P.A.hom _ ϖ * σ'.f j) →
        ∀ r : ℚ, NuGe D Q F v (k * N) s' r → ((r + (Q χ : ℚ) / k : ℚ) : WithTop ℚ) ≤ v c

def FinOrdExistsStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
    ∀ (p : QkPt D.toPre F k)
      (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))),
      w.IsGen → ∃ ζ : F, ζ ≠ 0 ∧ FinOrd D F k p w ζ

end ReciprocityTheory.ChartRestriction.G.H1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowAlg
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

def hv (θ : A → A → A → U) (k : ℕ) (a B x : A) : U := cubN θ k a B x * (θ a x B)⁻¹

theorem cub_rot (h : IsCub θ) (x y z : A) : θ x y z = θ y z x := by
  exact (h.s01 x y z).trans (h.s12 y x z)

private lemma prod_range_theta_mul_pow_eq_of_isCub (h : IsCub θ) (k : ℕ) (a M b x : A) :
    ∏ i ∈ Finset.range k, θ (a * M * b ^ i) b x =
      (∏ i ∈ Finset.range k, θ (M * b ^ i) b x) * θ a (M * b ^ k) x * (θ a M x)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
    have e := h.coc a (M * b ^ k) b x
    rw [← mul_assoc a M (b ^ k), mul_assoc M (b ^ k) b, ← pow_succ b k] at e
    have hA : θ (a * M * b ^ k) b x =
        θ a (M * b ^ (k + 1)) x * θ (M * b ^ k) b x * (θ a (M * b ^ k) x)⁻¹ := by
      rw [← e, mul_inv_cancel_right]
    rw [hA]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

private lemma mul_inv_rearrange_of_two_relations (Q G' G0 P R S T V W : U) (c1 : P * R = T * V) (c2 : T * G0 = W * S) :
    Q * G' * G0⁻¹ * P⁻¹ * R⁻¹ * S = Q * V⁻¹ * (G' * W⁻¹) := by
  have hS : S = W⁻¹ * (T * G0) := by rw [c2, inv_mul_cancel_left]
  have hP : P = T * V * R⁻¹ := by rw [← c1, mul_inv_cancel_right]
  subst hS hP
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, inv_inv]
  abel

theorem hv_term (h : IsCub θ) (k : ℕ) (a M b x : A) :
    hv θ k (a * M) b x * (θ a M b)⁻¹ * θ a x b = hv θ k M b x * (θ a (M * b ^ k) x * (θ a M (x * b))⁻¹) := by
  have c1 := h.coc a M x b
  have c2 : θ a (M * x) b * θ a M x = θ a M (x * b) * θ a x b := by
    have e := h.coc M x b a
    rw [← cub_rot h a (M * x) b, ← cub_rot h a M x, ← cub_rot h a M (x * b), ← cub_rot h a x b] at e
    exact e
  simp only [hv, cubN]
  rw [prod_range_theta_mul_pow_eq_of_isCub h]
  exact mul_inv_rearrange_of_two_relations _ _ _ _ _ _ _ _ _ c1 c2

private lemma eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq {X Y R S F1 F0 : U} (e : X * R⁻¹ * S = Y * (F1 * F0⁻¹)) :
    X = Y * (F1 / F0) * R * S⁻¹ := by
  rw [div_eq_mul_inv, ← e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem phiPow_indep (h : IsCub θ) (k : ℕ) (a b : A) :
    (∏ i ∈ Finset.range k, hv θ k (a * (b ^ k) ^ i) b (b ^ (k - 1 - i))) * cubN θ k 1 b a *
        (∏ i ∈ Finset.range k, θ a ((b ^ k) ^ i) b)⁻¹ =
      ∏ i ∈ Finset.range k, hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) := by
  have hf : ∀ i ∈ Finset.range k, hv θ k (a * (b ^ k) ^ i) b (b ^ (k - 1 - i)) =
      hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) *
        (θ a ((b ^ k) ^ (i + 1)) (b ^ (k - (i + 1))) / θ a ((b ^ k) ^ i) (b ^ (k - i))) *
        θ a ((b ^ k) ^ i) b * (θ a (b ^ (k - 1 - i)) b)⁻¹ := by
    intro i hi
    rw [Finset.mem_range] at hi
    have e := hv_term h k a ((b ^ k) ^ i) b (b ^ (k - 1 - i))
    have e1 : (b ^ k) ^ i * b ^ k = (b ^ k) ^ (i + 1) := (pow_succ _ _).symm
    have e2 : b ^ (k - 1 - i) * b = b ^ (k - i) := by
      rw [← pow_succ]
      congr 1
      omega
    have e3 : k - 1 - i = k - (i + 1) := by omega
    rw [e1, e2] at e
    rw [← e3]
    exact eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq e
  have tel : ∏ i ∈ Finset.range k,
      (θ a ((b ^ k) ^ (i + 1)) (b ^ (k - (i + 1))) / θ a ((b ^ k) ^ i) (b ^ (k - i))) =
      θ a ((b ^ k) ^ k) (b ^ (k - k)) / θ a ((b ^ k) ^ 0) (b ^ (k - 0)) :=
    Finset.prod_range_div (fun j => θ a ((b ^ k) ^ j) (b ^ (k - j))) k
  have f1 : θ a ((b ^ k) ^ k) (b ^ (k - k)) = 1 := by
    rw [Nat.sub_self, pow_zero, ← cub_rot h 1 a, h.face]
  have f0 : θ a ((b ^ k) ^ 0) (b ^ (k - 0)) = 1 := by
    rw [pow_zero, cub_rot h a 1, h.face]
  have refl : ∏ i ∈ Finset.range k, θ a (b ^ (k - 1 - i)) b = ∏ i ∈ Finset.range k, θ a (b ^ i) b :=
    Finset.prod_range_reflect (fun j => θ a (b ^ j) b) k
  have cub : cubN θ k 1 b a = ∏ i ∈ Finset.range k, θ a (b ^ i) b := by
    simp only [cubN]
    apply Finset.prod_congr rfl
    intro i _
    rw [one_mul, cub_rot h a (b ^ i) b]
  rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_inv_distrib, tel, refl, cub, f1, f0]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
  abel

end ReciprocityTheory.ChartRestriction.G.H1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SquareUnits
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TopologicalSpace Opposite

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic

variable {X Y Z : Scheme.{0}}

def UnitAt (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (y : Y) : Prop :=
  ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ J, Good L y J → IsUnit (sval s (𝟙 Y) y J)

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem UnitAt.mul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {y : Y}
    (h : UnitAt L φ ε y) (h' : UnitAt L φ' ε' y) : UnitAt L (Sum.elim φ φ') (Sum.elim ε ε') y := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs'⟩ := h'
  exact ⟨mulSec s s', fun J hJ => by rw [sval_mulSec s s' _ y hJ]; exact (hs J hJ).mul (hs' J hJ)⟩

theorem UnitAt.congr (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {y : Y}
    (hf : FormEq φ ε φ' ε') (h : UnitAt L φ ε y) : UnitAt L φ' ε' y := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs'⟩ := exists_sec hL hf s
  exact ⟨s', fun J hJ => by rw [hs' Y (𝟙 Y) y J hJ]; exact hs J hJ⟩

theorem formEq_of_add {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : ∀ (U : Type) [AddCommGroup U] (h : (Y ⟶ X) → U), ∑ k, ε k • h (φ k) = ∑ k, ε' k • h (φ' k)) :
    FormEq φ ε φ' ε' := by
  intro U _ h
  apply Additive.ofMul.injective
  simpa only [ofMul_prod, ofMul_zpow] using H (Additive U) (fun ψ => Additive.ofMul (h ψ))

theorem exists_sec_of_pullGen {Y' : Scheme.{0}} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y)
    (c : LB.Gen ((LB.LinComb L φ ε).pull h)) (hc : c.IsGen) :
    ∃ s : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε), ∀ (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι),
      Good L z J → IsUnit (sval s r z J) := by
  have l : ∀ j : K → L.ι, LB.wchart L (fun k => h ≫ φ k) j ≤
      LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => h) (fun _ => j) :=
    fun _ _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have e1 : ∀ (j : K → L.ι) (y : Y'), y ∈ LB.wchart L (fun k => h ≫ φ k) j →
      gs (𝟙 Y') y _ (res (l j) (c.s (fun _ => j))).val =
        (gm (𝟙 Y') y (LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => h) (fun _ => j)) (c.s (fun _ => j))).val :=
    fun j y hj => (gs_unit _ y _ hj _).trans (congrArg Units.val (gm_res _ y (l j) hj _))
  refine ⟨⟨fun j => (res (l j) (c.s (fun _ => j))).val, fun j j' => fn_ext fun y hy => ?_⟩, ?_⟩
  · refine ((gs_res (𝟙 Y') y _ hy _).trans (e1 j y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
        (congrArg Units.val (gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2))) ((gs_res (𝟙 Y') y _ hy _).trans
          (e1 j' y hy.2)))).symm)
    have m : ∀ j : K → L.ι, y ∈ LB.wchart L (fun k => h ≫ φ k) j → (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j :=
      fun j hj => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k
    rw [gen_trans hc (𝟙 Y') y (l j hy.1) (l j' hy.2), Units.val_mul]
    congr 2
    simp only [trF, Finset.univ_unique, Finset.prod_singleton, zpow_one]
    exact (gm_linComb L φ ε (𝟙 Y' ≫ h) y j j' (m j hy.1) (m j' hy.2)).trans (by simp only [Category.assoc])
  · intro r z J hJ
    have hm := hJ.mem (fun k => h ≫ φ k) r
    exact (congrArg IsUnit (gs_unit r z _ hm _)).mpr (Units.isUnit _)

section Square

variable {k : Type} [Field k]

theorem spec_pt_eq (q q' : Spec (CommRingCat.of k)) : q = q' := by
  have h1 : PrimeSpectrum.asIdeal (R := k) q = ⊥ := @Ideal.eq_bot_of_prime k _ _ (PrimeSpectrum.isPrime (R := k) q)
  have h2 : PrimeSpectrum.asIdeal (R := k) q' = ⊥ := @Ideal.eq_bot_of_prime k _ _ (PrimeSpectrum.isPrime (R := k) q')
  exact PrimeSpectrum.ext (h1.trans h2.symm)

theorem unitAt_square (hsq : SquareSt) (P : PolAV (Spec (CommRingCat.of k)))
    (x₁ x₂ : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (y : (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left) :
    UnitAt P.L ![(translPt P.A (x₁ * x₂)).left, (snd (baseOver (Spec (CommRingCat.of k))) P.A).left,
      (translPt P.A x₁).left, (translPt P.A x₂).left] ![1, 1, -1, -1] y := by
  obtain ⟨V, hpV, c, hc⟩ := hsq (Spec (CommRingCat.of k)) P (baseOver (Spec (CommRingCat.of k))) x₁ x₂
    (IsLocalRing.closedPoint k)
  have hV : V = ⊤ := eq_top_iff.2 fun q _ => by rw [spec_pt_eq q (IsLocalRing.closedPoint k)]; exact hpV
  subst hV
  obtain ⟨s, hs⟩ := exists_sec_of_pullGen (Z := (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left)
    ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι c hc
  let e := IsOpenImmersion.lift ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι (𝟙 _)
    (by rintro _ ⟨q, rfl⟩; rw [Scheme.Opens.range_ι]; trivial)
  have he : e ≫ ((fst (baseOver (Spec (CommRingCat.of k))) P.A).left ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    IsOpenImmersion.lift_fac _ _ _
  refine UnitAt.congr P.isLB ?_ ⟨pullSec s e, fun J hJ => ?_⟩
  · refine formEq_of_add fun U _ hh => ?_
    simp only [← Category.assoc, he, Category.id_comp]
  · rw [sval_pullSec s e (𝟙 _) y hJ]
    exact hs _ y J hJ

theorem unitAt_iter (hsq : SquareSt) (P : PolAV (Spec (CommRingCat.of k)))
    (b : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (y : (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left) :
    ∀ n : ℕ, UnitAt P.L ![(translPt P.A (b ^ (n + 2))).left, (snd (baseOver (Spec (CommRingCat.of k))) P.A).left,
      (translPt P.A b).left] ![1, (n : ℤ) + 1, -((n : ℤ) + 2)] y
  | 0 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_) (unitAt_square hsq P b b y)
    simp [Fin.sum_univ_succ, pow_two]
    module
  | n + 1 => by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((unitAt_iter hsq P b y n).mul (unitAt_square hsq P (b ^ (n + 2)) b y))
    have e : b ^ (n + 2) * b = b ^ (n + 1 + 2) := by rw [← pow_succ]
    simp [Fin.sum_univ_succ, e]
    module

end Square

end ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
end
end

