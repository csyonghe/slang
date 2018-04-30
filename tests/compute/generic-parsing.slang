//TEST(compute):COMPARE_COMPUTE:
//TEST_INPUT:ubuffer(data=[0 0 0 0], stride=4):dxbinding(0),glbinding(0),out
// Confirm that generics syntax can be used in user
// code and generates valid output.

RWStructuredBuffer<float4> outputBuffer;

interface IBxDF
{
    float getVal();
};

struct ShadingPoint<TBxDF : IBxDF>
{
    TBxDF bxdf;
};


[numthreads(1, 1, 1)]
void computeMain(uint3 dispatchThreadID : SV_DispatchThreadID)
{
    typedef BxDF<5> BT;
    typedef ShadingPoint<BT > BXDFType;
    BXDFType b;
    outputBuffer[0] = b.bxdf.getVal();
}

struct BxDF<let x: int>
{
    float getVal() {return x;}
};