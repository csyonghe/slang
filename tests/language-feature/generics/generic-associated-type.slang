//TEST(compute):COMPARE_COMPUTE(filecheck-buffer=CHECK): -shaderobj -output-using-type
//TEST(compute):COMPARE_COMPUTE(filecheck-buffer=CHECK): -vk -shaderobj -output-using-type

// Test that we can define a generic where one of the type parameter conforms to an generic interface parameterized on another
// type parameter.

interface IBar<T : __BuiltinIntegerType>
{
    T get();
}

interface IFoo<T : __BuiltinIntegerType>
{
    __generic<int n>
    associatedtype TA : IBar<T>;
    TA<n> getAssoc<int n>();
}

// struct TAParent<T:__BuiltinIntegerType>
// {
//     struct TAImpl<int n> : IBar<T>
//     {
//         T get()
//         {
//             return T(n);
//         }
//     }
// }

struct Foo<T : __BuiltinIntegerType> : IFoo<T>
{
    // typealias TA<int n> = TAParent<T>.TAImpl<n>;

    struct TA<int n> : IBar<T>
    {
        T get()
        {
            return T(n);
        }
    }
    TA<n> getAssoc<int n>()
    {
        return TA<n>();
    }
}

int helper<U:__BuiltinIntegerType, T:IFoo<U>>(T t)
{
    return t.getAssoc<1>().get().toInt();
}

//TEST_INPUT:ubuffer(data=[0 0 0 0], stride=4):out,name=outputBuffer
RWStructuredBuffer<int> outputBuffer;

[numthreads(1, 1, 1)]
void computeMain(int3 dispatchThreadID : SV_DispatchThreadID)
{
    Foo<int> obj1 = Foo<int>();
    
    // CHECK: 1
    outputBuffer[0] = helper(obj1);
}
