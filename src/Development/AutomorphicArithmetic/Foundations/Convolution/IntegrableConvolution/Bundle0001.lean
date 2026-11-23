module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C
open scoped ENNReal TensorProduct

namespace UpperTheory.ConvolutionTheory.L1

section Group

variable {G : Type*} [Group G] [MeasurableSpace G]

def cv (μ : Measure G) (a b : G → ℂ) : G → ℂ := fun x => ∫ y, a y * b (y⁻¹ * x) ∂μ

def cvAll (μ : Measure G) : (m : ℕ) → (Fin (m + 1) → G → ℂ) → G → ℂ
  | 0, φ => φ 0
  | m + 1, φ => cv μ (φ 0) (cvAll μ m (Fin.tail φ))

def cvPow (μ : Measure G) (a : G → ℂ) (k : ℕ) : G → ℂ := cvAll μ k fun _ => a

def fib {m : ℕ} (y : Fin m → G) (x : G) : Fin (m + 1) → G := Fin.snoc (α := fun _ => G) y ((List.ofFn y).prod⁻¹ * x)

def push (μ : Measure G) (m : ℕ) (Φ : (Fin (m + 1) → G) → ℂ) : G → ℂ :=
  fun x => ∫ y : Fin m → G, Φ (fib y x) ∂(Measure.pi fun _ => μ)

end Group

structure Split {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S] (ι : R →+* S) (s : S →+* S)
    (m : ℕ) where
  e : S ≃+* (Fin (m + 1) → R)
  cont : Continuous e
  cont_symm : Continuous e.symm
  map_diag : ∀ r i, e (ι r) i = r
  map_shift : ∀ x i, e (s x) i = e x (i + 1)

namespace Split

variable {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S] {ι : R →+* S} {s : S →+* S} {m : ℕ}

def comp (D : Split ι s m) (n : ℕ) (i : Fin (m + 1)) : GL (Fin n) S →* GL (Fin n) R :=
  mapGL n ((Pi.evalRingHom (fun _ : Fin (m + 1) => R) i).comp D.e.toRingHom)

def glue (D : Split ι s m) (n : ℕ) (g : Fin (m + 1) → GL (Fin n) R) : GL (Fin n) S where
  val := Matrix.of fun a b => D.e.symm fun i => (g i : Matrix (Fin n) (Fin n) R) a b
  inv := Matrix.of fun a b => D.e.symm fun i => ((g i)⁻¹ : GL (Fin n) R).val a b
  val_inv := by
    ext a b
    apply D.e.injective
    funext i
    have h := congrFun (congrFun (g i).val_inv a) b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, RingEquiv.apply_symm_apply, Finset.sum_apply,
      Pi.mul_apply] at h ⊢
    rw [show ((g i)⁻¹ : GL (Fin n) R).val = (g i).inv from rfl, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  inv_val := by
    ext a b
    apply D.e.injective
    funext i
    have h := congrFun (congrFun (g i).inv_val a) b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, RingEquiv.apply_symm_apply, Finset.sum_apply,
      Pi.mul_apply] at h ⊢
    rw [show ((g i)⁻¹ : GL (Fin n) R).val = (g i).inv from rfl, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

def transfer (D : Split ι s m) (n : ℕ) [MeasurableSpace (GL (Fin n) R)] (μ : Measure (GL (Fin n) R))
    (φ : GL (Fin n) S → ℂ) : GL (Fin n) R → ℂ := push μ m fun g => φ (D.glue n g)

def tens (D : Split ι s m) (n : ℕ) (φ : Fin (m + 1) → GL (Fin n) R → ℂ) : GL (Fin n) S → ℂ :=
  fun g => ∏ i, φ i (D.comp n i g)

end Split

def ChangeVar : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (m : ℕ)
    (δ : Fin (m + 1) → G),
    MeasurePreserving (fun x : Fin (m + 1) → G => (x 0, fun i : Fin m => (x i.castSucc)⁻¹ * δ i.castSucc * x i.succ))
      (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ => μ)) ∧
    ∀ x : Fin (m + 1) → G, (fun i => (x i)⁻¹ * δ i * x (i + 1)) =
      fib (fun i : Fin m => (x i.castSucc)⁻¹ * δ i.castSucc * x i.succ) ((x 0)⁻¹ * (List.ofFn δ).prod * x 0)

def PushTest : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (m : ℕ)
    (Φ : (Fin (m + 1) → G) → ℂ), Continuous Φ → HasCompactSupport Φ →
    Continuous (push μ m Φ) ∧ HasCompactSupport (push μ m Φ) ∧
      (∀ x, push μ m Φ x ≠ 0 → ∃ g, Φ g ≠ 0 ∧ (List.ofFn g).prod = x) ∧
      (∀ x, Integrable (fun y : Fin m → G => Φ (fib y x)) (Measure.pi fun _ => μ)) ∧
      (∀ c : ℂ, push μ m (c • Φ) = c • push μ m Φ) ∧
      ∀ Ψ : (Fin (m + 1) → G) → ℂ, Continuous Ψ → HasCompactSupport Ψ → push μ m (Φ + Ψ) = push μ m Φ + push μ m Ψ

def PushTens : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (m : ℕ)
    (φ : Fin (m + 1) → G → ℂ), (∀ i, Continuous (φ i)) → (∀ i, HasCompactSupport (φ i)) →
    push μ m (fun g => ∏ i, φ i (g i)) = cvAll μ m φ

def CvBasic : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (a b c : G → ℂ), Continuous a → HasCompactSupport a → Continuous b → HasCompactSupport b → Continuous c →
    HasCompactSupport c → Continuous (cv μ a b) ∧ HasCompactSupport (cv μ a b) ∧
      (∀ x, cv μ a b x ≠ 0 → ∃ y z, a y ≠ 0 ∧ b z ≠ 0 ∧ x = y * z) ∧
      cv μ (cv μ a b) c = cv μ a (cv μ b c) ∧ cv μ (a + b) c = cv μ a c + cv μ b c ∧ cv μ a (b + c) = cv μ a b + cv μ a c ∧
      ∀ t : ℂ, cv μ (t • a) b = t • cv μ a b ∧ cv μ a (t • b) = t • cv μ a b

def CvPowers : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (m : ℕ)
    (a ψ : G → ℂ), Continuous a → HasCompactSupport a → Continuous ψ → HasCompactSupport ψ → ∀ k : ℕ,
    (cvAll μ m (fun _ => cvPow μ a k) = cvPow μ (cvPow μ a m) k) ∧
    (cvAll μ m (Function.update (fun _ => cvPow μ a k) (Fin.last m) (cv μ (cvPow μ a k) ψ)) =
      cv μ (cvPow μ (cvPow μ a m) k) ψ) ∧
    ∀ φ φ' : Fin (m + 1) → G → ℂ, (∀ i, Continuous (φ i) ∧ HasCompactSupport (φ i)) →
      (∀ i, Continuous (φ' i) ∧ HasCompactSupport (φ' i)) →
      cv (Measure.pi fun _ => μ) (fun g : Fin (m + 1) → G => ∏ i, φ i (g i)) (fun g => ∏ i, φ' i (g i)) =
        fun g => ∏ i, cv μ (φ i) (φ' i) (g i)

def QuotAny : Prop :=
  ∀ (X T : Type) [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [MeasurableSpace T] [MeasurableInv T]
    (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [SFinite ν] [ν.IsInvInvariant] (i : T →* X), Measurable i →
    ∀ (Φ : X → ℂ) (ρ : X → ℝ≥0∞), Measurable Φ → (∀ t x, Φ (i t * x) = Φ x) → IsNormAlong id i ν ρ →
      ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤ → quotInt μ id i ν Φ = ∫ x, Φ x * ((ρ x).toReal : ℂ) ∂μ

def QuotFin : Prop :=
  ∀ (X T : Type) [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
    [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant] (i : T →* X), Continuous i →
    ∀ (Φ : X → ℂ) (ρ : X → ℝ≥0∞), Continuous Φ → (∀ t x, Φ (i t * x) = Φ x) →
      (∃ C, IsCompact C ∧ ∀ x, Φ x ≠ 0 → ∃ t, ∃ y ∈ C, x = i t * y) →
      IsNormAlong id i ν ρ → ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ < ⊤

def ClosedProper : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] (γ : G), IsClosed {y | ∃ x, y = x⁻¹ * γ * x} → ∀ D : Set G, IsCompact D →
    ∃ C : Set G, IsCompact C ∧ ∀ x, x⁻¹ * γ * x ∈ D → ∃ t ∈ Subgroup.centralizer {γ}, ∃ y ∈ C, x = t * y

def GeoAbs : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (m : ℕ) (γ : G),
    IsClosed {y | ∃ x, y = x⁻¹ * γ * x} → (∀ a ∈ Subgroup.centralizer {γ}, ∀ b ∈ Subgroup.centralizer {γ}, a * b = b * a) →
    ∀ (ν : Measure (Subgroup.centralizer {γ})) [ν.IsHaarMeasure] (δ : Fin (m + 1) → G),
      (∀ i, δ i ∈ Subgroup.centralizer {γ}) → (List.ofFn δ).prod = γ →
      ∀ Φ : (Fin (m + 1) → G) → ℂ, Continuous Φ → HasCompactSupport Φ →
      (∀ ρ, IsNormAlong id (fun t : Subgroup.centralizer {γ} => fun _ : Fin (m + 1) => (t : G)) ν ρ →
        ∫⁻ x, ‖Φ fun i => (x i)⁻¹ * δ i * x (i + 1)‖ₑ * ρ x ∂(Measure.pi fun _ => μ) < ⊤) ∧
      quotInt (Measure.pi fun _ => μ) id (fun t : Subgroup.centralizer {γ} => fun _ : Fin (m + 1) => (t : G)) ν
          (fun x => Φ fun i => (x i)⁻¹ * δ i * x (i + 1)) =
        quotInt μ id (fun t : Subgroup.centralizer {γ} => (t : G)) ν fun x => push μ m Φ (x⁻¹ * γ * x)

def RegOk (R : Type) [CommRing R] [TopologicalSpace R] (n : ℕ) : Prop :=
  ∀ γ : GL (Fin n) R, (γ : Matrix (Fin n) (Fin n) R).charpoly.Separable →
    IsClosed {y | ∃ x : GL (Fin n) R, y = x⁻¹ * γ * x} ∧
      ∀ a ∈ Subgroup.centralizer {γ}, ∀ b ∈ Subgroup.centralizer {γ}, a * b = b * a

def RegOkPi : Prop :=
  (∀ (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] (n : ℕ), RegOk k n) ∧
  (∀ (I : Type) (k : I → Type) [∀ i, Field (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsTopologicalRing (k i)]
    [∀ i, T2Space (k i)] (n : ℕ), RegOk (∀ i, k i) n) ∧
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), RegOk (InfiniteAdeleRing F) n

def GlueBasic : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R]
    [IsTopologicalRing S] (ι : R →+* S) (s : S →+* S) (m : ℕ) (D : Split ι s m) (n : ℕ),
    (∀ g i, D.comp n i (D.glue n g) = g i) ∧ (∀ x, D.glue n (fun i => D.comp n i x) = x) ∧
      (∀ g h, D.glue n (g * h) = D.glue n g * D.glue n h) ∧ Continuous (D.glue n) ∧ (∀ i, Continuous (D.comp n i)) ∧
      (∀ t i, D.comp n i (mapGL n ι t) = t) ∧ (∀ x i, D.comp n i (mapGL n s x) = D.comp n (i + 1) x) ∧
      ∀ (δ : GL (Fin n) S) (γ : GL (Fin n) R), twNorm (mapGL n s) (m + 1) δ = mapGL n ι γ ↔
        (∀ i, D.comp n i δ ∈ Subgroup.centralizer {γ}) ∧ (List.ofFn fun i => D.comp n i δ).prod = γ ∧
          ∀ j : Fin (m + 1), (List.ofFn fun i => D.comp n (j + i) δ).prod = γ

def MatchSplit : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R]
    [IsTopologicalRing S] [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R] (ι : R →+* S) (s : S →+* S) (m : ℕ)
    (D : Split ι s m) (n : ℕ) [MeasurableSpace (GL (Fin n) R)] [BorelSpace (GL (Fin n) R)] [MeasurableSpace (GL (Fin n) S)]
    [BorelSpace (GL (Fin n) S)] (μS : Measure (GL (Fin n) S)) (μR : Measure (GL (Fin n) R)), μS.IsHaarMeasure →
    μR.IsHaarMeasure → RegOk R n → ∃ c : ℝ, 0 < c ∧
      μS = ENNReal.ofReal c • Measure.map (D.glue n) (Measure.pi fun _ => μR) ∧
      ∀ φ : GL (Fin n) S → ℂ, Continuous φ → HasCompactSupport φ →
        Continuous (D.transfer n μR φ) ∧ HasCompactSupport (D.transfer n μR φ) ∧
          Match ι s (m + 1) μS μR c φ (D.transfer n μR φ)

def GalSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ m : ℕ, Module.finrank F E = m + 1 →
    ∀ (A B : Type) [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e₀ : E ⊗[F] A ≃ₐ[E] B) (p : E →ₐ[F] A),
    ∃ e : B ≃+* (Fin (m + 1) → A), (∀ x a i, e (e₀ (x ⊗ₜ a)) i = p ((σ ^ (i : ℕ)) x) * a) ∧
      ∀ b i, e (galOf e₀ σ b) i = e b (i + 1)

def InfSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ m : ℕ, Module.finrank F E = m + 1 →
    (IsTotallyComplex F → Nonempty (E →ₐ[F] InfiniteAdeleRing F)) ∧
    ∀ p : E →ₐ[F] InfiniteAdeleRing F,
      ∃ D : Split (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) (galInf σ) m,
        ∀ (x : E) i, D.e (algebraMap E (InfiniteAdeleRing E) x) i = p ((σ ^ (i : ℕ)) x)

def FinSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ m : ℕ, Module.finrank F E = m + 1 →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (w₀ : PlacesOver E v), (∀ w : PlacesOver E v, Function.Surjective (completionMap v w.1)) →
    ∃ (D : Split (incFin E v) (galFin σ v) m) (w : Fin (m + 1) ≃ PlacesOver E v), w 0 = w₀ ∧
      ∀ (b : CompletionsOver E v) i, completionMap v (w i).1 (D.e b i) = b (w i)

def MatchInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m : ℕ)
    (D : Split (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) (galInf σ) m) (n : ℕ)
    [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing E))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing E))]
    [MeasurableSpace (GL (Fin n) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin n) (InfiniteAdeleRing F))]
    (μE : Measure (GL (Fin n) (InfiniteAdeleRing E))) (μF : Measure (GL (Fin n) (InfiniteAdeleRing F))),
    μE.IsHaarMeasure → μF.IsHaarMeasure → ∃ c : ℝ, 0 < c ∧
      μE = ENNReal.ofReal c • Measure.map (D.glue n) (Measure.pi fun _ => μF) ∧
      (∀ φ, Continuous φ → HasCompactSupport φ →
        Match (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) (galInf σ) (m + 1) μE μF c φ
          (D.transfer n μF φ)) ∧
      ∀ φ : Fin (m + 1) → GL (Fin n) (InfiniteAdeleRing F) → ℂ, (∀ i, Continuous (φ i) ∧ HasCompactSupport (φ i)) →
        Continuous (D.tens n φ) ∧ HasCompactSupport (D.tens n φ) ∧ D.transfer n μF (D.tens n φ) = cvAll μF m φ

def MatchFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (D : Split (incFin E v) (galFin σ v) m) (n : ℕ)
    [MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [BorelSpace (GL (Fin n) (CompletionsOver E v))]
    [MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [BorelSpace (GL (Fin n) (v.adicCompletion F))]
    (μE : Measure (GL (Fin n) (CompletionsOver E v))) (μF : Measure (GL (Fin n) (v.adicCompletion F))),
    μE.IsHaarMeasure → μF.IsHaarMeasure → ∃ c : ℝ, 0 < c ∧
      μE = ENNReal.ofReal c • Measure.map (D.glue n) (Measure.pi fun _ => μF) ∧
      (∀ φ, Continuous φ → HasCompactSupport φ → Match (incFin E v) (galFin σ v) (m + 1) μE μF c φ (D.transfer n μF φ)) ∧
      ∀ φ : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) → ℂ, (∀ i, Continuous (φ i) ∧ HasCompactSupport (φ i)) →
        Continuous (D.tens n φ) ∧ HasCompactSupport (D.tens n φ) ∧ D.transfer n μF (D.tens n φ) = cvAll μF m φ

end UpperTheory.ConvolutionTheory.L1
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TrDefs
section
noncomputable section

open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C

namespace UpperTheory.ConvolutionTheory.L1

def MatImage : Prop :=
  ∀ (A W : Type) [Ring A] [Algebra ℂ A] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (ρ : A →ₐ[ℂ] Module.End ℂ W) (B : Set (Module.End ℂ W)), (∀ a, ∀ b ∈ B, Commute (ρ a) b) →
    (∀ P : Submodule ℂ W, (∀ a, ∀ w ∈ P, ρ a w ∈ P) → (∀ b ∈ B, ∀ w ∈ P, b w ∈ P) → P = ⊥ ∨ P = ⊤) →
    ∃ d : ℕ, 0 < d ∧ Nonempty (ρ.range ≃ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)

def UnitsTrace : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (m d : ℕ)
    (r : Fin (m + 1) → (Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ W)), (∀ i j, i ≠ j → ∀ a b, Commute (r i a) (r j b)) →
    (∀ P : Submodule ℂ W, (∀ i a, ∀ w ∈ P, r i a w ∈ P) → P = ⊥ ∨ P = ⊤) →
    ∀ U : W ≃ₗ[ℂ] W, (∀ i a w, U (r (i + 1) a w) = r i a (U w)) →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (i₀ : Fin (m + 1)) (S : Module.End ℂ W), (∀ j, j ≠ i₀ → ∀ a, Commute S (r j a)) →
      LinearMap.trace ℂ W (S ∘ₗ (U : W →ₗ[ℂ] W)) = c * LinearMap.trace ℂ W S

def AlgTrace : Prop :=
  ∀ (W X : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (m : ℕ) (T : Fin (m + 1) → X → Module.End ℂ W),
    (∀ i j, i ≠ j → ∀ x y, Commute (T i x) (T j y)) →
    (∀ P : Submodule ℂ W, (∀ i x, ∀ w ∈ P, T i x w ∈ P) → P = ⊥ ∨ P = ⊤) →
    ∀ U : W ≃ₗ[ℂ] W, (∀ i x w, U (T (i + 1) x w) = T i x (U w)) →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (i₀ : Fin (m + 1)) (S : Module.End ℂ W), (∀ j, j ≠ i₀ → ∀ x, Commute S (T j x)) →
      LinearMap.trace ℂ W (S ∘ₗ (U : W →ₗ[ℂ] W)) = c * LinearMap.trace ℂ W S

structure Slots {Γ G H : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : UnitaryRep Γ H) (V : Submodule ℂ H) (m : ℕ) (ι : Fin (m + 1) → G →* Γ) (E : H →L[ℂ] H)
    (A : Fin (m + 1) → H →L[ℂ] H) (U : H ≃ₗᵢ[ℂ] H) : Prop where
  summand : IsSummandOf π ⊤ V
  ι_comm : ∀ i j, i ≠ j → ∀ g h, Commute (ι i g) (ι j h)
  rest : ∀ γ : Γ, ∃ (g : Fin (m + 1) → G) (γ' : Γ) (c : ℂ), γ = (List.ofFn fun i => ι i (g i)).prod * γ' ∧
    ∀ v ∈ V, E (π γ' (E v)) = c • E v
  E_sa : IsSelfAdjoint E
  E_idem : ∀ v, E (E v) = E v
  E_mem : ∀ v ∈ V, E v ∈ V
  E_ι : ∀ i g v, E (π (ι i g) v) = π (ι i g) (E v)
  A_pos : ∀ i, 0 ≤ A i
  A_mem : ∀ i, ∀ v ∈ V, A i v ∈ V
  A_E : ∀ i v, A i (E v) = E (A i v)
  A_A : ∀ i j v, A i (A j v) = A j (A i v)
  A_ι : ∀ i j, i ≠ j → ∀ g v, A i (π (ι j g) v) = π (ι j g) (A i v)
  U_mem : V.map (U : H →ₗ[ℂ] H) = V
  U_E : ∀ v, U (E v) = E (U v)
  U_A : ∀ i v, U (A (i + 1) v) = A i (U v)
  U_ι : ∀ i g v, U (π (ι (i + 1) g) v) = π (ι i g) (U v)

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {m : ℕ}

def prodEig (V : Submodule ℂ H) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H) (x : ℝ) : Submodule ℂ H :=
  eigIn (eigIn V E 1) (List.ofFn A).prod x

def jointEig (V : Submodule ℂ H) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H) (y : ℝ) : Submodule ℂ H :=
  ⨅ i, eigIn (eigIn V E 1) (A i) y
end

def CutIrr : Prop :=
  ∀ (Γ G H : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (V : Submodule ℂ H) (m : ℕ) (ι : Fin (m + 1) → G →* Γ) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H)
    (U : H ≃ₗᵢ[ℂ] H), Slots π V m ι E A U →
    IsClosed (eigIn V E 1 : Set H) ∧ (∀ i g, ∀ v ∈ eigIn V E 1, π (ι i g) v ∈ eigIn V E 1) ∧
      ∀ P ≤ eigIn V E 1, IsClosed (P : Set H) → (∀ i g, ∀ v ∈ P, π (ι i g) v ∈ P) → P = ⊥ ∨ P = eigIn V E 1

def JointNe : Prop :=
  ∀ (Γ G H : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (V : Submodule ℂ H) (m : ℕ) (ι : Fin (m + 1) → G →* Γ) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H)
    (U : H ≃ₗᵢ[ℂ] H), Slots π V m ι E A U → ∀ (i : Fin (m + 1)) (y : ℝ), eigIn (eigIn V E 1) (A i) y ≠ ⊥ → jointEig V E A y ≠ ⊥

def JointEx : Prop :=
  ∀ (Γ G H : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (V : Submodule ℂ H) (m : ℕ) (ι : Fin (m + 1) → G →* Γ) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H)
    (U : H ≃ₗᵢ[ℂ] H), Slots π V m ι E A U → IsCompactOperator ((List.ofFn A).prod ∘L prj (eigIn V E 1)) →
    (∀ x : ℝ, 0 < x → FiniteDimensional ℂ (prodEig V E A x)) ∧
      ((∃ i, ∃ v ∈ eigIn V E 1, A i v ≠ 0) → ∃ y : ℝ, 0 < y ∧ jointEig V E A y ≠ ⊥)

def DiagOnly : Prop :=
  ∀ (Γ G H : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (V : Submodule ℂ H) (m : ℕ) (ι : Fin (m + 1) → G →* Γ) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H)
    (U : H ≃ₗᵢ[ℂ] H), Slots π V m ι E A U → ∀ y : ℝ, 0 < y → FiniteDimensional ℂ (prodEig V E A (y ^ (m + 1))) →
    jointEig V E A y ≤ prodEig V E A (y ^ (m + 1)) ∧
    ∀ (i₀ : Fin (m + 1)) (S : H →L[ℂ] H), (∀ j, j ≠ i₀ → ∀ v, S (A j v) = A j (S v)) →
      trOn (prodEig V E A (y ^ (m + 1))) (S ∘L (U : H →L[ℂ] H)) = trOn (jointEig V E A y) (S ∘L (U : H →L[ℂ] H))

def JointTrace : Prop :=
  ∀ (Γ G H : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (V : Submodule ℂ H) (m : ℕ) (ι : Fin (m + 1) → G →* Γ) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H)
    (U : H ≃ₗᵢ[ℂ] H), Slots π V m ι E A U → ∀ y : ℝ, FiniteDimensional ℂ (jointEig V E A y) →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (i₀ : Fin (m + 1)) (S : H →L[ℂ] H), (∀ j, j ≠ i₀ → ∀ v, S (A j v) = A j (S v)) →
      (∀ j, j ≠ i₀ → ∀ g v, S (π (ι j g) v) = π (ι j g) (S v)) →
      trOn (jointEig V E A y) (S ∘L (U : H →L[ℂ] H)) = c * trOn (jointEig V E A y) S

def TwTrace : Prop :=
  ∀ (Γ G H : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (V : Submodule ℂ H) (m : ℕ) (ι : Fin (m + 1) → G →* Γ) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H)
    (U : H ≃ₗᵢ[ℂ] H), Slots π V m ι E A U → ∀ y : ℝ, 0 < y → FiniteDimensional ℂ (prodEig V E A (y ^ (m + 1))) →
    ∃ c : ℂ, c ≠ 0 ∧
      trOn (prodEig V E A (y ^ (m + 1))) (U : H →L[ℂ] H) = c * Module.finrank ℂ (jointEig V E A y) ∧
      ∀ (i₀ : Fin (m + 1)) (S : H →L[ℂ] H), (∀ j, j ≠ i₀ → ∀ v, S (A j v) = A j (S v)) →
        (∀ j, j ≠ i₀ → ∀ g v, S (π (ι j g) v) = π (ι j g) (S v)) →
        trOn (prodEig V E A (y ^ (m + 1))) (S ∘L (U : H →L[ℂ] H)) = c * trOn (jointEig V E A y) S

end UpperTheory.ConvolutionTheory.L1
end
end

