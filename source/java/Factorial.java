public class Factorial
{
	
	public int factorial(int n)
	{	int result = 1;
                int i = 0;
		for(i = 2; i <= n; i++)
			result *= i;
		return result;
	}
}
