[ExperimentalModule]
module tile;

#define TILE_DIM_PARAMS int dim0, int dim1, int dim2, int dim3, int dim4, int dim5, int dim6, int dim7
#define TILE_DIM_ARGS dim0, dim1, dim2, dim3, dim4, dim5, dim6, dim7

enum RoundingMode
{
    Default,
    RoundTiesToEven,
    RoundTowardZero,
    RoundTowardNegative,
    RoundTowardPositive,
    RoundApproximate,
    RoundFull,
}

enum SubnormalsRoundingMode
{
    Preserve,
    RoundToZero,
}

enum PaddingMode
{
    Undefined,
    Zero,
    NegZero,
    Nan,
    PosInf,
    NegInf,
}

enum Latency
{
    Default = 0,
    Level1,
    Level2,
    Level3,
    Level4,
    Level5,
    Level6,
    Level7,
    Level8,
    Level9,
    Level10,
}

[require(tile)]
struct TensorDesc<T:ICoopElement, PaddingMode paddingMode = PaddingMode.Undefined>
{
    __init(T* basePtr);

    This withShape(int dim0, int dim1=0, int dim2=0, int dim3=0, int dim4=0, int dim5=0, int dim6=0, int dim7=0);
    This withStride(int stride0, int stride1=0, int stride2=0, int stride3=0, int stride4=0, int stride5=0, int stride6=0, int stride7=0);
}

__intrinsic_op(castIntToFloat)
internal Tile<T, TILE_DIM_ARGS> __int_to_float_cast<T:ICoopElement, U:ICoopElement, TILE_DIM_PARAMS>(Tile<U, TILE_DIM_ARGS> tile);

__intrinsic_op(castFloatToInt)
internal Tile<T, TILE_DIM_ARGS> __float_to_int_cast<T:ICoopElement, U:ICoopElement, TILE_DIM_PARAMS>(Tile<U, TILE_DIM_ARGS> tile);

__intrinsic_op(floatCast)
internal Tile<T, TILE_DIM_ARGS> __float_cast<T:ICoopElement, U:ICoopElement, TILE_DIM_PARAMS>(Tile<U, TILE_DIM_ARGS> tile);

__intrinsic_op(intCast)
internal Tile<T, TILE_DIM_ARGS> __int_cast<T:ICoopElement, U:ICoopElement, TILE_DIM_PARAMS>(Tile<U, TILE_DIM_ARGS> tile);


[require(tile)]
struct Tile<T:ICoopElement, int dim0, int dim1=0, int dim2=0, int dim3=0, int dim4=0, int dim5=0, int dim6=0, int dim7=0>
{
    static This arrange();
    static This ones();
    static This zeros();
    static This fill(T value);

    static const int kConversionCost_ScalarToTile = 15;
    __implicit_conversion(15)
    __init(T value)
    {
        return fill(value);
    }

    [ForceInline]
    __init<U:ICoopElement>(Tile<U, TILE_DIM_ARGS> other)
    {
        if (T is bool)
        {
            if (U is bool)
                return __slang_noop_cast<Tile<T, TILE_DIM_ARGS>>(other);
            else
                return other != U(0);
        }
        else if (U is bool)
        {
            return select(other, Tile<T, TILE_DIM_ARGS>(T(1)), Tile<T, TILE_DIM_ARGS>(T(0)));
        }
        if (__isFloat<T>() && __isInt<U>())
            return __int_to_float_cast<T>(other);
        else if (__isInt<T>() && __isFloat<U>())
            return __float_to_int_cast<T>(other);
        else if (__isFloat<T>() && __isFloat<U>())
            return __float_cast<T>(other);
        else if (__isInt<T>() && __isInt<U>())
            return __int_cast<T>(other);
    }

    This prefixSum<int axis, RoundingMode roundingMode = RoundingMode.Default, SubnormalsRoundingMode subnormalRounding = SubnormalsRoundingMode.Preserve>();
    This prefixProduct<int axis, RoundingMode roundingMode = RoundingMode.Default, SubnormalsRoundingMode subnormalRounding = SubnormalsRoundingMode.Preserve>();

    This reduceSum<int axis, RoundingMode roundingMode = RoundingMode.Default, SubnormalsRoundingMode subnormalRounding = SubnormalsRoundingMode.Preserve>();
    This reduceProduct<int axis, RoundingMode roundingMode = RoundingMode.Default, SubnormalsRoundingMode subnormalRounding = SubnormalsRoundingMode.Preserve>();
    This reduceMin<int axis>();
    This reduceMax<int axis>();
    This reduceBitAnd<int axis>();
    This reduceBitOr<int axis>();
    This reduceBitXor<int axis>();

    static This gather<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, Tile<uint, TILE_DIM_ARGS> indices, T paddingValue=T(0), Latency latency=Latency.Default);

    void scatter<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, Tile<uint, TILE_DIM_ARGS> indices, Latency latency=Latency.Default);

    // Returns old value.
    This atomicCompareExchange<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, Tile<uint, TILE_DIM_ARGS> indices, Tile<T, TILE_DIM_ARGS> compareValue, Tile<T, TILE_DIM_ARGS> newValue);

    // Returns old value.
    This atomicExchange<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, Tile<uint, TILE_DIM_ARGS> indices, Tile<T, TILE_DIM_ARGS> newValue);

    This atomicAdd<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, Tile<uint, TILE_DIM_ARGS> indices, Tile<T, TILE_DIM_ARGS> value);
    This atomicMax<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, Tile<uint, TILE_DIM_ARGS> indices, Tile<T, TILE_DIM_ARGS> value);
    This atomicMin<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, Tile<uint, TILE_DIM_ARGS> indices, Tile<T, TILE_DIM_ARGS> value);
    This atomicAnd<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, Tile<uint, TILE_DIM_ARGS> indices, Tile<T, TILE_DIM_ARGS> value);
    This atomicOr<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, Tile<uint, TILE_DIM_ARGS> indices, Tile<T, TILE_DIM_ARGS> value);
    This atomicXor<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, Tile<uint, TILE_DIM_ARGS> indices, Tile<T, TILE_DIM_ARGS> value);

    Tile<T, n0, n1, n2, n3, n4, n5, n6, n7> reshape<int n0, int n1, int n2, int n3, int n4, int n5, int n6, int n7, T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> tile);
    Tile<T, n0, n1, n2, n3, n4, n5, n6, n7> broadcast<int n0, int n1, int n2, int n3, int n4, int n5, int n6, int n7, T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> tile);
    __transposeTileType(Tile<T, TILE_DIM_ARGS>, axis0, axis1) transpose<int axis0, int axis1>();
    __permuateTileType(Tile<T, TILE_DIM_ARGS>, p0, p1, p2, p3, p4, p5, p6, p7) permuate<int p0, int p1, int p2=0, int p3=0, int p4=0, int p5=0, int p6=0, int p7=0>();
    __expandDimTileType(Tile<T, TILE_DIM_ARGS>, axis) expandDim<int axis>();
}

extension<T:ICoopElement, int dim0> Tile<T, dim0>
{
    Tile<T, nd0> extract<int nd0>(int index0);
    static This load<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, Latency latency=Latency.Default);
    void store<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, Latency latency=Latency.Default);
}

extension<T:ICoopElement, int dim0, int dim1> Tile<T, dim0, dim1>
{
    Tile<T, nd0, nd1> extract<int nd0, int nd1>(int index0, int index1);
    static This load<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, int index1, Latency latency=Latency.Default);
    void store<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, int index1, Latency latency=Latency.Default);
}

extension<T:ICoopElement, int dim0, int dim1, int dim2> Tile<T, dim0, dim1, dim2>
{
    Tile<T, nd0, nd1, nd2> extract<int nd0, int nd1, int nd2>(int index0, int index1, int index2);
    static This load<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, int index1, int index2, Latency latency=Latency.Default);
    void store<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, int index1, int index2, Latency latency=Latency.Default);
}

extension<T:ICoopElement, int dim0, int dim1, int dim2, int dim3> Tile<T, dim0, dim1, dim2, dim3>
{
    Tile<T, nd0, nd1, nd2, nd3> extract<int nd0, int nd1, int nd2, int nd3>(int index0, int index1, int index2, int index3);
    static This load<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, int index1, int index2, int index3, Latency latency=Latency.Default);
    void store<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, int index1, int index2, int index3, Latency latency=Latency.Default);
}

extension<T:ICoopElement, int dim0, int dim1, int dim2, int dim3, int dim4> Tile<T, dim0, dim1, dim2, dim3, dim4>
{
    Tile<T, nd0, nd1, nd2, nd3, nd4> extract<int nd0, int nd1, int nd2, int nd3, int nd4>(int index0, int index1, int index2, int index3, int index4);
    static This load<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, int index1, int index2, int index3, int index4, Latency latency=Latency.Default);
    void store<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, int index1, int index2, int index3, int index4, Latency latency=Latency.Default);
}

extension<T:ICoopElement, int dim0, int dim1, int dim2, int dim3, int dim4, int dim5> Tile<T, dim0, dim1, dim2, dim3, dim4, dim5>
{
    Tile<T, nd0, nd1, nd2, nd3, nd4, nd5> extract<int nd0, int nd1, int nd2, int nd3, int nd4, int nd5>(int index0, int index1, int index2, int index3, int index4, int index5);
    static This load<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, int index1, int index2, int index3, int index4, int index5, Latency latency=Latency.Default);
    void store<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, int index1, int index2, int index3, int index4, int index5, Latency latency=Latency.Default);
}

extension<T:ICoopElement, int dim0, int dim1, int dim2, int dim3, int dim4, int dim5, int dim6> Tile<T, dim0, dim1, dim2, dim3, dim4, dim5, dim6>
{
    Tile<T, nd0, nd1, nd2, nd3, nd4, nd5, nd6> extract<int nd0, int nd1, int nd2, int nd3, int nd4, int nd5, int nd6>(int index0, int index1, int index2, int index3, int index4, int index5, int index6);
    static This load<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, int index1, int index2, int index3, int index4, int index5, int index6, Latency latency=Latency.Default);
    void store<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, int index1, int index2, int index3, int index4, int index5, int index6, Latency latency=Latency.Default);
}

extension<T:ICoopElement, int dim0, int dim1, int dim2, int dim3, int dim4, int dim5, int dim6, int dim7> Tile<T, dim0, dim1, dim2, dim3, dim4, dim5, dim6, dim7>
{
    Tile<T, nd0, nd1, nd2, nd3, nd4, nd5, nd6, nd7> extract<int nd0, int nd1, int nd2, int nd3, int nd4, int nd5, int nd6, int nd7>(int index0, int index1, int index2, int index3, int index4, int index5, int index6, int index7);
    static This load<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, int index1, int index2, int index3, int index4, int index5, int index6, int index7, Latency latency=Latency.Default);
    void store<PaddingMode paddingMode>(TensorDesc<T, paddingMode> ptr, int index0, int index1, int index2, int index3, int index4, int index5, int index6, int index7, Latency latency=Latency.Default);
}

Tile<bool, TILE_DIM_ARGS> all<int axis, TILE_DIM_PARAMS>(Tile<bool, TILE_DIM_ARGS> a);
Tile<bool, TILE_DIM_ARGS> any<int axis, TILE_DIM_PARAMS>(Tile<bool, TILE_DIM_ARGS> a);

Tile<T, a0+bdim, a1, a2, a3, a4, a5, a6, a7> concatAxis0<
    T:ICoopElement,int a0, int a1, int a2, int a3, int a4, int a5, int a6, int a7, int bdim>(
    Tile<T, a0, a1, a2, a3, a4, a5, a6, a7> a,
    Tile<T, bdim, a1, a2, a3, a4, a5, a6, a7> b);
Tile<T, a0, a1+bdim, a2, a3, a4, a5, a6, a7> concatAxis1<
    T:ICoopElement,int a0, int a1, int a2, int a3, int a4, int a5, int a6, int a7, int bdim>(
    Tile<T, a0, a1, a2, a3, a4, a5, a6, a7> a,
    Tile<T, a0, bdim, a2, a3, a4, a5, a6, a7> b);
Tile<T, a0, a1, a2+bdim, a3, a4, a5, a6, a7> concatAxis2<
    T:ICoopElement,int a0, int a1, int a2, int a3, int a4, int a5, int a6, int a7, int bdim>(
    Tile<T, a0, a1, a2, a3, a4, a5, a6, a7> a,
    Tile<T, a0, a1, bdim, a3, a4, a5, a6, a7> b);
Tile<T, a0, a1, a2, a3+bdim, a4, a5, a6, a7> concatAxis3<
    T:ICoopElement,int a0, int a1, int a2, int a3, int a4, int a5, int a6, int a7, int bdim>(
    Tile<T, a0, a1, a2, a3, a4, a5, a6, a7> a,
    Tile<T, a0, a1, a2, bdim, a4, a5, a6, a7> b);
Tile<T, a0, a1, a2, a3, a4+bdim, a5, a6, a7> concatAxis4<
    T:ICoopElement,int a0, int a1, int a2, int a3, int a4, int a5, int a6, int a7, int bdim>(
    Tile<T, a0, a1, a2, a3, a4, a5, a6, a7> a,
    Tile<T, a0, a1, a2, a3, bdim, a5, a6, a7> b);
Tile<T, a0, a1, a2, a3, a4, a5+bdim, a6, a7> concatAxis5<
    T:ICoopElement,int a0, int a1, int a2, int a3, int a4, int a5, int a6, int a7, int bdim>(
    Tile<T, a0, a1, a2, a3, a4, a5, a6, a7> a,
    Tile<T, a0, a1, a2, a3, a4, bdim, a6, a7> b);
Tile<T, a0, a1, a2, a3, a4, a5, a6+bdim, a7> concatAxis6<
    T:ICoopElement,int a0, int a1, int a2, int a3, int a4, int a5, int a6, int a7, int bdim>(
    Tile<T, a0, a1, a2, a3, a4, a5, a6, a7> a,
    Tile<T, a0, a1, a2, a3, a4, a5, bdim, a7> b);
Tile<T, a0, a1, a2, a3, a4, a5, a6, a7+bdim> concatAxis7<
    T:ICoopElement,int a0, int a1, int a2, int a3, int a4, int a5, int a6, int a7, int bdim>(
    Tile<T, a0, a1, a2, a3, a4, a5, a6, a7> a,
    Tile<T, a0, a1, a2, a3, a4, a5, a6, bdim> b);


__intrinsic_op(add)
Tile<T, TILE_DIM_ARGS> operator +<T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

__intrinsic_op(sub)
Tile<T, TILE_DIM_ARGS> operator -<T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

__intrinsic_op(mul)
Tile<T, TILE_DIM_ARGS> operator *<T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

__intrinsic_op(div)
Tile<T, TILE_DIM_ARGS> operator /<T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

__intrinsic_op(frem)
Tile<T, TILE_DIM_ARGS> operator %<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

__intrinsic_op(irem)
Tile<T, TILE_DIM_ARGS> operator %<T:__BuiltinIntegerType, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

__intrinsic_op(shl)
Tile<T, TILE_DIM_ARGS> operator << <T:__BuiltinIntegerType, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

__intrinsic_op(shr)
Tile<T, TILE_DIM_ARGS> operator >> <T:__BuiltinIntegerType, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

__prefix
__intrinsic_op(neg)
Tile<T, TILE_DIM_ARGS> operator -<T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

__prefix
__intrinsic_op(bitnot)
Tile<T, TILE_DIM_ARGS> operator ~<T:__BuiltinIntegerType, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

__prefix
__intrinsic_op(not)
Tile<bool, TILE_DIM_ARGS> operator !<T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

__intrinsic_op(cmpGT)
Tile<bool, TILE_DIM_ARGS> operator > <T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

__intrinsic_op(cmpGE)
Tile<bool, TILE_DIM_ARGS> operator >= <T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

__intrinsic_op(cmpLT)
Tile<bool, TILE_DIM_ARGS> operator < <T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

__intrinsic_op(cmpLE)
Tile<bool, TILE_DIM_ARGS> operator <= <T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

__intrinsic_op(cmpEQ)
Tile<bool, TILE_DIM_ARGS> operator ==<T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

__intrinsic_op(cmpNE)
Tile<bool, TILE_DIM_ARGS> operator !=<T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

__intrinsic_op(select)
Tile<T, TILE_DIM_ARGS> select<T:ICoopElement, TILE_DIM_PARAMS>(Tile<bool, TILE_DIM_ARGS> condition, Tile<T, TILE_DIM_ARGS> trueValue, Tile<T, TILE_DIM_ARGS> falseValue);

Tile<T, B, M, N> matMul<T:ICoopElement, int B, int M, int K, int N>(Tile<T, B, M, K> a, Tile<T, B, K, N> b);

Tile<T, B, M, N> matMulAdd<T:ICoopElement, int B, int M, int K, int N>(Tile<T, B, M, K> a, Tile<T, B, K, N> b, Tile<T, B, M, N> c);

Tile<T, TILE_DIM_ARGS> min<T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

Tile<T, TILE_DIM_ARGS> max<T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

Tile<T, TILE_DIM_ARGS> pow<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a, Tile<T, TILE_DIM_ARGS> b);

Tile<T, TILE_DIM_ARGS> abs<T:ICoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

Tile<T, TILE_DIM_ARGS> exp<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

Tile<T, TILE_DIM_ARGS> exp2<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

Tile<T, TILE_DIM_ARGS> log<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

Tile<T, TILE_DIM_ARGS> log2<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

Tile<T, TILE_DIM_ARGS> sqrt<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

Tile<T, TILE_DIM_ARGS> rsqrt<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

Tile<T, TILE_DIM_ARGS> sin<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

Tile<T, TILE_DIM_ARGS> cos<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

Tile<T, TILE_DIM_ARGS> tan<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

Tile<T, TILE_DIM_ARGS> sinh<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

Tile<T, TILE_DIM_ARGS> cosh<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

Tile<T, TILE_DIM_ARGS> tanh<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

Tile<T, TILE_DIM_ARGS> floor<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);

Tile<T, TILE_DIM_ARGS> ceil<T:IFloatingPointCoopElement, TILE_DIM_PARAMS>(Tile<T, TILE_DIM_ARGS> a);



void test()
{
    Tile<float, 4> a = 1.0f;
    let c = a + 3.0f;
    let d = 1.0f + c;
}