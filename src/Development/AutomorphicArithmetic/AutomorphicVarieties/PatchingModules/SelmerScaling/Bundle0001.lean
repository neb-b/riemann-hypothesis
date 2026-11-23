module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.UrepStable

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlgebraMapMemSecondOrder
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa.SelmerFractionFieldBaseChange

variable {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (F : Type) [CommRing F] [Algebra x.A F]

end UpperTheory.V.Pa.SelmerFractionFieldBaseChange

private theorem selMap2_lemma {R S Γ : Type} [CommRing R] [CommRing S] [TopologicalSpace Γ] (I : Ideal R) (J : Ideal S)
    (π : R →+ S) (hπ : ∀ N u, u ∈ I ^ N → π u ∈ J ^ N) (f : Γ → R) (hf : AdicCont I f) :
    AdicCont J (fun g => π (f g)) := by
  intro N
  have hs := Ideal.Quotient.mk_surjective (I := I ^ N)
  have e : (fun g => Ideal.Quotient.mk (J ^ N) (π (f g))) =
      (fun q => Ideal.Quotient.mk (J ^ N) (π (Function.surjInv hs q))) ∘
        (fun g => Ideal.Quotient.mk (I ^ N) (f g)) := by
    funext g
    simp only [Function.comp]
    rw [Ideal.Quotient.eq, ← map_sub]
    apply hπ
    rw [← Ideal.Quotient.eq]
    exact (Function.surjInv_eq hs _).symm
  rw [e]
  exact (hf N).comp _

private theorem dd_components_mem_span_pow_of_mem_span_algebraMap_pow {A : Type} [CommRing A] (g : ℕ) (t : A) (N : ℕ) (u : DD A g)
    (hu : u ∈ Ideal.span {algebraMap A (DD A g) t} ^ N) :
    u.a ∈ Ideal.span {t} ^ N ∧ (∀ j, u.ep j ∈ Ideal.span {t} ^ N) ∧ (∀ j, u.ep' j ∈ Ideal.span {t} ^ N) ∧
      u.eta ∈ Ideal.span {t} ^ N := by
  rw [Ideal.span_singleton_pow, ← map_pow, Ideal.mem_span_singleton'] at hu
  obtain ⟨r, rfl⟩ := hu
  rw [Ideal.span_singleton_pow]
  have ha : (algebraMap A (DD A g) (t ^ N)).a = t ^ N := rfl
  have he : (algebraMap A (DD A g) (t ^ N)).ep = 0 := rfl
  have he' : (algebraMap A (DD A g) (t ^ N)).ep' = 0 := rfl
  have hη : (algebraMap A (DD A g) (t ^ N)).eta = 0 := rfl
  refine ⟨?_, fun j => ?_, fun j => ?_, ?_⟩
  · rw [DD.mul_a, ha]
    exact Ideal.mem_span_singleton'.mpr ⟨r.a, rfl⟩
  · rw [DD.mul_ep, ha, he]
    exact Ideal.mem_span_singleton'.mpr ⟨r.ep j, by simp⟩
  · rw [DD.mul_ep', ha, he']
    exact Ideal.mem_span_singleton'.mpr ⟨r.ep' j, by simp⟩
  · rw [DD.mul_eta, ha, he, he', hη]
    exact Ideal.mem_span_singleton'.mpr ⟨r.eta, by simp⟩

private theorem dd_map_algebraMap_algebraMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (g : ℕ) (c : A) :
    DD.map (algebraMap A B) (algebraMap A (DD A g) c) = algebraMap A (DD B g) c :=
  DD.ext rfl (funext fun _ => map_zero _) (funext fun _ => map_zero _) (map_zero _)

private theorem dd_map_mem_span_algebraMap_pow {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (g : ℕ) (t : A) (N : ℕ) (u : DD A g)
    (hu : u ∈ Ideal.span {algebraMap A (DD A g) t} ^ N) :
    DD.map (algebraMap A B) u ∈ Ideal.span {algebraMap A (DD B g) t} ^ N := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hu ⊢
  obtain ⟨r, rfl⟩ := hu
  exact ⟨DD.map (algebraMap A B) r, by rw [map_mul, map_pow, dd_map_algebraMap_algebraMap]⟩

private theorem ddMap_algebraMap_mem_ddPart {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (g : ℕ) (b1 b2 b3 b4 : Bool)
    (u : DD A g) (hu : u ∈ ddPart A A g b1 b2 b3 b4) : DD.map (algebraMap A B) u ∈ ddPart A B g b1 b2 b3 b4 := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · show algebraMap A B u.a = 0
    rw [h1 h, map_zero]
  · show (fun j => algebraMap A B (u.ep j)) = 0
    rw [h2 h]
    funext j
    exact map_zero _
  · show (fun j => algebraMap A B (u.ep' j)) = 0
    rw [h3 h]
    funext j
    exact map_zero _
  · show algebraMap A B u.eta = 0
    rw [h4 h, map_zero]

private theorem map_ddMap_algebraMap_mem_W2 {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n g a : ℕ)
    (Z : Matrix (Fin n) (Fin n) (DD A g)) (hZ : Z ∈ W2 n A A g a) :
    Z.map (DD.map (algebraMap A B)) ∈ W2 n A B g a := by
  intro i j
  exact ⟨fun hc => ddMap_algebraMap_mem_ddPart g _ _ _ _ _ ((hZ i j).1 hc), fun hc => ddMap_algebraMap_mem_ddPart g _ _ _ _ _ ((hZ i j).2 hc)⟩

private theorem map_algebraMap_map_ddMap_algebraMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n g : ℕ)
    (M : Matrix (Fin n) (Fin n) A) :
    (M.map (algebraMap A (DD A g))).map (DD.map (algebraMap A B)) = M.map (algebraMap A (DD B g)) := by
  exact Matrix.ext fun i j => dd_map_algebraMap_algebraMap (A := A) (B := B) g (M i j)

private theorem epM_map_ddMap_algebraMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n g : ℕ)
    (Z : Fin g → Matrix (Fin n) (Fin n) A) :
    (DD.epM Z).map (DD.map (algebraMap A B)) = DD.epM (fun j => (Z j).map (algebraMap A B)) := by
  refine Matrix.ext fun i j => DD.ext ?_ ?_ ?_ ?_
  · exact map_zero (algebraMap A B)
  · rfl
  · funext m
    exact map_zero (algebraMap A B)
  · exact map_zero (algebraMap A B)

private theorem kap_rho1_map_ddMap_algebraMap {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (B : Type)
    [CommRing B] [Algebra x.A B] (g : Fm.G₀) :
    (k.ρ1 x.A g).map (DD.map (algebraMap x.A B)) = k.ρ1 B g := by
  have e : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A B)) = (DD.map (algebraMap x.A B)).mapMatrix M := fun _ => rfl
  unfold Kap.ρ1 NP.ρX
  rw [e, map_mul, map_add (f := _), map_one, ← e, ← e, epM_map_ddMap_algebraMap, map_algebraMap_map_ddMap_algebraMap]
  rfl

private theorem w1_map_dd_map_algebraMap {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (B : Type)
    [CommRing B] [Algebra x.A B] (v : Fm.Vl) :
    (k.w1 x.A v).map (DD.map (algebraMap x.A B)) = k.w1 B v := by
  have e : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A B)) = (DD.map (algebraMap x.A B)).mapMatrix M := fun _ => rfl
  unfold Kap.w1 NP.wX
  rw [e, map_mul, map_sub, map_one, ← e, ← e, epM_map_ddMap_algebraMap, map_algebraMap_map_ddMap_algebraMap]
  rfl

private theorem wi1_map_dd_map_algebraMap {l : ℕ} [Fact l.Prime] {Fm : GFrame l} {n : ℕ} {x : NP Fm n} (k : Kap x) (B : Type)
    [CommRing B] [Algebra x.A B] (v : Fm.Vl) :
    (k.wi1 x.A v).map (DD.map (algebraMap x.A B)) = k.wi1 B v := by
  have e : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A B)) = (DD.map (algebraMap x.A B)).mapMatrix M := fun _ => rfl
  unfold Kap.wi1 NP.wiX
  rw [e, map_mul, map_add (f := _), map_one, ← e, ← e, epM_map_ddMap_algebraMap, map_algebraMap_map_ddMap_algebraMap]
  rfl

private theorem selMap2_lemma_12 {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) {R S : Type} [CommRing R] [CommRing S]
    (Φ : R →+* S) (ρ z : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)
    (ρ' z' : F.G₀ → Matrix (Fin n) (Fin n) S) (w' wi' : F.Vl → Matrix (Fin n) (Fin n) S)
    (hρ : ∀ g, ρ' g = (ρ g).map Φ) (hz : ∀ g, z' g = (z g).map Φ) (hw : ∀ v, w' v = (w v).map Φ)
    (hwi : ∀ v, wi' v = (wi v).map Φ) (v : F.Vl) (Y : Matrix (Fin n) (Fin n) R)
    (hL : LocAt F ρ w wi z v Y) : LocAt F ρ' w' wi' z' v (Y.map Φ) := by
  have eM : ∀ M : Matrix (Fin n) (Fin n) R, M.map Φ = Φ.mapMatrix M := fun _ => rfl
  intro g
  obtain ⟨h1, h2⟩ := hL g
  have e : wi' v * (z' (F.φ v g) - dY F ρ' (Y.map Φ) (F.φ v g)) * w' v =
      (wi v * (z (F.φ v g) - dY F ρ Y (F.φ v g)) * w v).map Φ := by
    simp only [dY, hρ, hz, hw, hwi, eM, map_mul, map_sub]
  refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
  · rw [e, Matrix.map_apply, h1 i j hij, map_zero]
  · rw [e, Matrix.map_apply, h2 hg i, map_zero]

open UpperTheory.V.Pa.SelmerFractionFieldBaseChange in
theorem UpperTheory.V.Pa.selMap2 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ z ∈ Sel2 h x.A k, (fun g => (z g).map (DD.map (algebraMap x.A x.Fr))) ∈ Sel2 h x.Fr k ∧ BndD x.t fun g => (z g).map (DD.map (algebraMap x.A x.Fr)) := by
  intro l _ L G G0 h n x k z hz
  obtain ⟨hV, hC, hco, hcj, hIu, hloc⟩ := hz
  have eM : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g),
      M.map (DD.map (algebraMap x.A x.Fr)) = (DD.map (algebraMap x.A x.Fr)).mapMatrix M := fun _ => rfl
  refine ⟨⟨fun g => map_ddMap_algebraMap_mem_W2 n k.g x.a _ (hV g), fun i j => ?_, fun g1 g2 => ?_, fun g => ?_,
    fun u g hg => ?_, fun v => ?_⟩, fun i j => ⟨?_, fun m => ?_, fun m => ?_, ?_⟩⟩
  · exact selMap2_lemma _ _ (DD.map (algebraMap x.A x.Fr)).toAddMonoidHom
      (fun N u hu => dd_map_mem_span_algebraMap_pow k.g x.t N u hu) (fun g => z g i j) (hC i j)
  · beta_reduce
    beta_reduce at hco
    rw [hco g1 g2, ← kap_rho1_map_ddMap_algebraMap k x.Fr, ← kap_rho1_map_ddMap_algebraMap k x.Fr]
    simp only [eM, map_add (f := _), map_mul]
  · beta_reduce
    rw [hcj g]
    exact Matrix.ext fun i j => map_neg (DD.map (algebraMap x.A x.Fr)) (z g j i)
  · beta_reduce
    rw [hIu u g hg]
    exact Matrix.map_zero _ (map_zero _)
  · obtain ⟨Y, hY, hL⟩ := hloc v
    exact ⟨Y.map (DD.map (algebraMap x.A x.Fr)), map_ddMap_algebraMap_mem_W2 n k.g x.a _ hY,
      selMap2_lemma_12 G.frame (DD.map (algebraMap x.A x.Fr)) _ z _ _ _ _ _ _
        (fun g => (kap_rho1_map_ddMap_algebraMap k x.Fr _).symm) (fun g => rfl) (fun v => (w1_map_dd_map_algebraMap k x.Fr v).symm)
        (fun v => (wi1_map_dd_map_algebraMap k x.Fr v).symm) v Y hL⟩
  · refine ⟨0, fun g => (z g i j).a, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.a, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).1) (fun g => z g i j) (hC i j)
  · refine ⟨0, fun g => (z g i j).ep m, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.ep m, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).2.1 m) (fun g => z g i j) (hC i j)
  · refine ⟨0, fun g => (z g i j).ep' m, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.ep' m, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).2.2.1 m) (fun g => z g i j) (hC i j)
  · refine ⟨0, fun g => (z g i j).eta, ?_, fun g => by rw [pow_zero, one_mul]; rfl⟩
    exact selMap2_lemma _ _ { toFun := fun u : DD x.A k.g => u.eta, map_zero' := rfl, map_add' := fun _ _ => rfl }
      (fun N u hu => (dd_components_mem_span_pow_of_mem_span_algebraMap_pow k.g x.t N u hu).2.2.2) (fun g => z g i j) (hC i j)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.BndOps
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section SlopeTestRemainingChoices
variable {A Fr G : Type} [CommRing A] [CommRing Fr] [Algebra A Fr] [TopologicalSpace G] {I : Ideal A} {t : A}

private theorem ac_const (c : A) : AdicCont I fun _ : G => c := fun _ => IsLocallyConstant.const _

end SlopeTestRemainingChoices

private theorem adicCont_add_and_adicCont_mul {R G : Type} [CommRing R] [TopologicalSpace G] {I : Ideal R} {φ ψ : G → R}
    (hφ : AdicCont I φ) (hψ : AdicCont I ψ) :
    AdicCont I (fun g => φ g + ψ g) ∧ AdicCont I (fun g => φ g * ψ g) := by
  unfold AdicCont at *
  constructor
  · intro N
    simpa [map_add (f := _)] using (hφ N).comp₂ (hψ N) (· + ·)
  · intro N
    simpa [map_mul] using (hφ N).comp₂ (hψ N) (· * ·)

private theorem adicCont_neg_of_adicCont {R G : Type} [CommRing R] [TopologicalSpace G] {I : Ideal R} {φ : G → R}
    (hφ : AdicCont I φ) : AdicCont I (fun g => -φ g) := by
  unfold AdicCont at *
  intro N
  simpa [map_neg, Function.comp_def] using (hφ N).comp (fun y => -y)

private theorem adicCont_comp_inv_of_isTopologicalGroup {R G : Type} [CommRing R] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {I : Ideal R} {φ : G → R} (hφ : AdicCont I φ) : AdicCont I (fun g => φ g⁻¹) := by
  unfold AdicCont at *
  intro N
  exact (hφ N).comp_continuous continuous_inv

theorem UpperTheory.V.Pa.bndOps :
    ∀ (K G : Type) [Field K] [TopologicalSpace G] [Group G] [IsTopologicalGroup G], (∀ c : FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) fun _ : G => c) ∧ (∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ → BndF (PowerSeries.X : PowerSeries K) ψ → (BndF (PowerSeries.X : PowerSeries K) fun g => φ g + ψ g) ∧ (BndF (PowerSeries.X : PowerSeries K) fun g => φ g * ψ g) ∧ (BndF (PowerSeries.X : PowerSeries K) fun g => -φ g) ∧ BndF (PowerSeries.X : PowerSeries K) fun g => φ g⁻¹) ∧ (∀ (ι : Type) (s : Finset ι) (φ : ι → G → FractionRing (PowerSeries K)), (∀ i ∈ s, BndF (PowerSeries.X : PowerSeries K) (φ i)) → BndF (PowerSeries.X : PowerSeries K) fun g => ∑ i ∈ s, φ i g) ∧ (∀ φ : G → PowerSeries K, AdicCont (Ideal.span {(PowerSeries.X : PowerSeries K)}) φ → BndF (PowerSeries.X : PowerSeries K) fun g => algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (φ g)) ∧ ∀ (φ : G → FractionRing (PowerSeries K)), BndF (PowerSeries.X : PowerSeries K) φ → ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∃ φ' : G → PowerSeries K, AdicCont (Ideal.span {(PowerSeries.X : PowerSeries K)}) φ' ∧ ∀ g, algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (φ' g) = algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ^ s * φ g := by
  intro K G _ _ _ _
  have hconst : ∀ c : FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) fun _ : G => c := by
    intro c
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (PowerSeries K)) c
    have hb : (b : PowerSeries K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    obtain ⟨v, hv⟩ := PowerSeries.isUnit_divided_by_X_pow_order hb
    obtain ⟨n, hbv⟩ : ∃ n : ℕ, (b : PowerSeries K) = PowerSeries.X ^ n * (v : PowerSeries K) :=
      ⟨(b : PowerSeries K).order.toNat, by rw [hv, PowerSeries.X_pow_order_mul_divXPowOrder]⟩
    have hb0 : algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))).mpr hb
    unfold BndF
    refine ⟨n, fun _ => a * ↑v⁻¹, ac_const _, fun _ => ?_⟩
    dsimp only
    rw [IsFractionRing.mk'_eq_div, mul_div_assoc', eq_div_iff hb0,
      ← map_mul (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))),
      ← map_pow (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))),
      ← map_mul (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))]
    congr 1
    rw [hbv, show a * ↑v⁻¹ * (PowerSeries.X ^ n * ↑v) = PowerSeries.X ^ n * a * (↑v⁻¹ * ↑v) by ring,
      Units.inv_mul, mul_one]
  have hops : ∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ →
      BndF (PowerSeries.X : PowerSeries K) ψ →
      (BndF (PowerSeries.X : PowerSeries K) fun g => φ g + ψ g) ∧
      (BndF (PowerSeries.X : PowerSeries K) fun g => φ g * ψ g) ∧
      (BndF (PowerSeries.X : PowerSeries K) fun g => -φ g) ∧
      BndF (PowerSeries.X : PowerSeries K) fun g => φ g⁻¹ := by
    intro φ ψ hφ hψ
    unfold BndF at hφ hψ ⊢
    obtain ⟨s1, φ1, hc1, he1⟩ := hφ
    obtain ⟨s2, ψ2, hc2, he2⟩ := hψ
    refine ⟨⟨s1 + s2, fun g => PowerSeries.X ^ s2 * φ1 g + PowerSeries.X ^ s1 * ψ2 g, ?_, fun g => ?_⟩,
      ⟨s1 + s2, fun g => φ1 g * ψ2 g, (adicCont_add_and_adicCont_mul hc1 hc2).2, fun g => ?_⟩,
      ⟨s1, fun g => -φ1 g, adicCont_neg_of_adicCont hc1, fun g => ?_⟩,
      ⟨s1, fun g => φ1 g⁻¹, adicCont_comp_inv_of_isTopologicalGroup hc1, fun g => he1 g⁻¹⟩⟩
    · exact (adicCont_add_and_adicCont_mul (adicCont_add_and_adicCont_mul (ac_const _) hc1).2 (adicCont_add_and_adicCont_mul (ac_const _) hc2).2).1
    · simp only [map_add (f := _), map_mul, map_pow, he1, he2]
      ring
    · simp only [map_mul, he1, he2]
      ring
    · simp only [map_neg, he1]
      ring
  refine ⟨hconst, hops, ?_, ?_, ?_⟩
  · intro ι s φ hφ
    classical
    revert hφ
    refine Finset.induction_on s ?_ ?_
    · intro _
      simpa using hconst 0
    · intro a t hat ih hall
      have h1 := hall a (Finset.mem_insert_self a t)
      have h2 := ih (fun i hi => hall i (Finset.mem_insert_of_mem hi))
      simp only [Finset.sum_insert hat]
      exact (hops _ _ h1 h2).1
  · intro φ hφ
    unfold BndF
    exact ⟨0, φ, hφ, fun g => by simp⟩
  · intro φ hφ
    unfold BndF at hφ
    obtain ⟨s0, φ0, hc0, he0⟩ := hφ
    refine ⟨s0, fun s hs => ⟨fun g => PowerSeries.X ^ (s - s0) * φ0 g, (adicCont_add_and_adicCont_mul (ac_const _) hc0).2, fun g => ?_⟩⟩
    rw [map_mul, map_pow, he0, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hs]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.BndRho
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem bnd_of {A Fr Γ Γ' : Type} [CommRing A] [CommRing Fr] [Algebra A Fr] [TopologicalSpace Γ]
    [TopologicalSpace Γ'] (t : A) (φ : Γ' → A) (hφ : AdicCont (Ideal.span {t}) φ) (p : Γ → Γ') (hp : Continuous p) :
    BndF t fun g => algebraMap A Fr (φ (p g)) :=
  ⟨0, fun g => φ (p g), fun N => (hφ N).comp_continuous hp, fun g => by simp⟩

theorem UpperTheory.V.Pa.bndRho :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), BndM x.t (fun g : G.G₀ => x.ρX x.Fr (h.p₀ g)) ∧ BndM x.t (fun g : G.G₀ => x.ρX x.Fr (h.p₀ g⁻¹)) ∧ ∀ j, BndM x.t (kapF h k j) := by
  intro l _ L G G0 h n x k
  have hp : Continuous (h.p₀ : G.G₀ → G0.G₀) := by
    apply Continuous.subtype_mk
    exact h.cont.comp continuous_subtype_val
  have hpi : Continuous (fun g : G.G₀ => h.p₀ g⁻¹) := hp.comp continuous_inv
  have hρ : ∀ i j, AdicCont (Ideal.span {x.t}) (fun g : G0.G₀ => (mat x.ρ) g i j) := by
    intro i j
    have := x.cont i j
    rwa [PowerSeries.maximalIdeal_eq_span_X] at this
  refine ⟨fun i j => bnd_of x.t _ (hρ i j) _ hp, fun i j => bnd_of x.t _ (hρ i j) _ hpi, ?_⟩
  intro j i i'
  have hk := ((k.mem j).2.1 i i')
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hk
  exact bnd_of x.t _ hk _ hp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.ClosureIdeal
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem chi_rep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [Matrix.charpoly, Matrix.charmatrix]
  congr 1
  rw [map_sub, MonoidAlgebra.mapRingHom_single, map_one]
  ext i j : 2
  simp [GDet.repAlg, Matrix.one_apply, Matrix.diagonal_apply]

private theorem rep_single {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Algebra B A] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) (b : B) :
    GDet.repAlg ρ A (MonoidAlgebra.mapRingHom G (algebraMap B A) (MonoidAlgebra.single g b)) =
      algebraMap B A b • ρ g := by
  rw [MonoidAlgebra.mapRingHom_single]
  ext i j
  simp [GDet.repAlg]

theorem UpperTheory.V.Pa.vrRel :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), (∀ v (g : Fin S.n → S.L.Gv v), (List.ofFn fun i => S.U.vr (S.G.φ v (g i)) - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.u.ψ v i (g i)))).prod = 0) ∧ (∀ w, ∀ g ∈ S.G.frame.Iu w, S.U.vr g = 1) ∧ (∀ j, (List.ofFn fun i => S.U.vr (S.P.ph j) - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.P.U j i))).prod = 0) ∧ (∀ j i, (List.ofFn fun k => if k = i then 1 else S.U.vr (S.P.ph j) - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.P.U j k))).prod * (S.U.vr (S.P.ta j) - 1 - algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA (S.P.y j i))) = 0) ∧ ∀ i g, algebraMap S.B S.U.AA (S.u.D.lam i (MonoidAlgebra.single g 1)) = (-1) ^ i * (S.U.vr g).charpoly.coeff (S.n - i) := by
  intro l _ S
  let Φ : MonoidAlgebra S.B S.G.G₀ →+* Matrix (Fin S.n) (Fin S.n) S.U.AA :=
    (GDet.repAlg S.U.vr S.U.AA).toRingHom.comp (MonoidAlgebra.mapRingHom S.G.G₀ (algebraMap S.B S.U.AA))
  have h1 : ∀ g : S.G.G₀, Φ (MonoidAlgebra.single g 1) = S.U.vr g := fun g =>
    (rep_single S.U.vr g (1 : S.B)).trans (by rw [map_one, one_smul])
  have h2 : ∀ b : S.B, Φ (MonoidAlgebra.single 1 b) =
      algebraMap S.U.AA (Matrix (Fin S.n) (Fin S.n) S.U.AA) (algebraMap S.B S.U.AA b) := fun b =>
    (rep_single S.U.vr 1 b).trans (by rw [map_one, Algebra.algebraMap_eq_smul_one (A := Matrix _ _ _)])
  have hk : ∀ z ∈ pairGens S.u ∪ qGens (O := S.O) (F := S.G.frame) S.P.ph S.P.ta S.P.U S.P.y, Φ z = 0 := by
    intro z hz
    refine S.U.kills z ?_
    change z ∈ S.u.D.chBar _
    simp only [GDet.chBar, closureIdeal, TwoSidedIdeal.mem_iInf]
    exact fun N H => TwoSidedIdeal.subset_span (Or.inl (Or.inl (Or.inr hz)))
  refine ⟨fun v g => ?_, fun w g hg => ?_, fun j => ?_, fun j i => ?_, fun i g => ?_⟩
  · rw [← hk (S.G.frame.oEl v (S.u.ψ v) g) (Or.inl (Or.inl ⟨v, g, Or.inl rfl⟩)), GFrame.oEl, map_list_prod,
      List.map_ofFn]
    congr 2
    funext i
    dsimp only [Function.comp_apply]
    rw [map_sub, h1, h2]
  · have := hk _ (Or.inl (Or.inr ⟨w, g, (S.P.Ip w).symm ▸ hg, Or.inl rfl⟩))
    rwa [map_sub, h1, map_one, sub_eq_zero] at this
  · rw [← hk _ (Or.inr (Or.inl ⟨j, Or.inl rfl⟩)), q1El, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    dsimp only [Function.comp_apply]
    rw [map_sub, h1, h2]
  · rw [← hk _ (Or.inr (Or.inr ⟨j, i, Or.inl rfl⟩)), q2El, map_mul, map_list_prod, List.map_ofFn, map_sub, map_sub,
      h1, h2, map_one]
    congr 3
    funext k
    dsimp only [Function.comp_apply]
    split_ifs
    · rw [map_one]
    · rw [map_sub, h1, h2]
  · rw [← ((UpperTheory.V.CA.d_gmap S.u.D).2.2.1 (algebraMap S.B S.U.AA) _).2 i, S.U.det, MonoidAlgebra.mapRingHom_single,
      map_one, GDet.lam, chi_rep]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.DiscImp
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.discImp :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ Q : Ideal S.Bh, Q.IsPrime → DiscSt (S.u.D.map (algebraMap S.B S.Bh)) Q → S.x.a = S.n ∨ ¬ ired S.U.N ≤ Q := by
  intro l _ S Q hQ hs
  rcases (UpperTheory.V.Pa.urep_stable S.U Q hQ).1 hs with ha | ⟨y, hy, z, hz, b, hb, e⟩
  · exact Or.inl ha
  · exact Or.inr fun hle => hb (hle (Ideal.subset_span ⟨y, hy, z, hz, e⟩))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.ExistsSemilinearFunctionalNonzero
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_semilinear_functional_nonzero {O B F M : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Field F] [AddCommGroup M]
    [Module B M] (φ : O →+* B) (f : O →+* F) (hf : Function.Surjective f)
    (hM : ∀ o ∈ maximalIdeal O, ∀ m : M, φ o • m = 0) (q : M) (hq : q ≠ 0) :
    ∃ Φ : M →+ F, (∀ o m, Φ (φ o • m) = f o * Φ m) ∧ Φ q ≠ 0 := by
  letI : Module O M := Module.compHom M φ
  haveI hmax : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  have hker : RingHom.ker f = maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
  have hT : Module.IsTorsionBySet O M (RingHom.ker f) := by
    rintro m ⟨o, ho⟩
    exact hM o (hker ▸ ho) m
  letI : Field (O ⧸ RingHom.ker f) := Ideal.Quotient.field _
  letI : Module (O ⧸ RingHom.ker f) M := hT.module
  haveI : Module.Free (O ⧸ RingHom.ker f) M := Module.Free.of_divisionRing _ _
  haveI : Module.Projective (O ⧸ RingHom.ker f) M := Module.Projective.of_free
  obtain ⟨Ψ, hΨ⟩ := Module.Projective.exists_dual_ne_zero (O ⧸ RingHom.ker f) hq
  let e := RingHom.quotientKerEquivOfSurjective hf
  refine ⟨(e : (O ⧸ RingHom.ker f) →+* F).toAddMonoidHom.comp Ψ.toAddMonoidHom, fun o m => ?_, ?_⟩
  · show e (Ψ (φ o • m)) = f o * e (Ψ m)
    have hs : (φ o • m : M) = (Ideal.Quotient.mk (RingHom.ker f) o) • m := (hT.mk_smul o m).symm
    rw [hs, map_smul, smul_eq_mul, map_mul, RingHom.quotientKerEquivOfSurjective_apply_mk]
  · show e (Ψ q) ≠ 0
    exact fun h => hΨ (e.injective (h.trans (map_zero e).symm))

theorem UpperTheory.V.Pa.phSep :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ y : S.U.N, (∀ Φ ∈ S.Ph, Φ y = 0) → y ∈ S.J2 • (⊤ : Submodule S.Bh S.U.N) := by
  intro l _ S y hy
  by_contra hne
  let P := S.J2 • (⊤ : Submodule S.Bh S.U.N)
  have hq : (Submodule.Quotient.mk y : S.U.N ⧸ P) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hne
  have hJ : ∀ b ∈ S.J2, ∀ z : S.U.N, b • z ∈ P := fun b hb z => Submodule.smul_mem_smul hb trivial
  have hM : ∀ o ∈ maximalIdeal S.OO, ∀ m : S.U.N ⧸ P, algebraMap S.OO S.Bh o • m = 0 := by
    intro o ho m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective P m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hJ _ (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ho))) z
  obtain ⟨Φ0, hΦ0, hne0⟩ :=
    exists_semilinear_functional_nonzero (algebraMap S.OO S.Bh) (S.rF.comp (algebraMap S.OO S.Bh)) S.oo_surj hM _ hq
  let Φ : S.U.N →+ S.F := Φ0.comp P.mkQ.toAddMonoidHom
  have hmem : Φ ∈ S.Ph := by
    refine ⟨fun o z => ?_, fun b hb z => ?_⟩
    · show Φ0 (P.mkQ (algebraMap S.OO S.Bh o • z)) = S.rF (algebraMap S.OO S.Bh o) * Φ0 (P.mkQ z)
      rw [map_smul]
      exact hΦ0 o _
    · show Φ0 (P.mkQ (b • z)) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).mpr (hJ b hb z), map_zero]
  exact hne0 (hy Φ hmem)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.HomBasic
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.homBasic :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0), Function.Surjective h.p₀ ∧ Continuous h.p₀ ∧ (∀ g, h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g)) ∧ (∀ v g, h.p₀ (G.φ v g) = G0.φ v g) ∧ (∀ w, ∀ g ∈ G.frame.Iu w, h.p₀ g ∈ G0.frame.Iu w) ∧ ∀ (O R : Type) [CommRing O] [Algebra ℤ_[l] O] [CommRing R] [Algebra O R] (g : G.G₀), G0.frame.eps O R (h.p₀ g) = G.frame.eps O R g := by
  intro l _ L G G0 h
  refine ⟨fun g => ?_, (h.cont.comp continuous_subtype_val).subtype_mk _, fun g => Subtype.ext ?_,
    fun v g => Subtype.ext (h.φ v g), ?_, fun O R _ _ _ _ g => ?_⟩
  · obtain ⟨a, ha⟩ := h.surj g
    exact ⟨⟨a, by rw [MonoidHom.mem_ker, ← h.η, ha]; exact g.2⟩, Subtype.ext ha⟩
  · change h.p (G.c * g * G.c⁻¹) = G0.c * h.p g * G0.c⁻¹
    rw [map_mul, map_mul, map_inv, h.c]
  · rintro w _ ⟨j, hj, rfl⟩
    exact ⟨j, hj, Subtype.ext (h.φu w j).symm⟩
  · change Units.map _ (G0.ε (h.p g)) = Units.map _ (G.ε g)
    rw [h.ε]
end

