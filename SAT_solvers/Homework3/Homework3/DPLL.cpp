#include<iostream>
#include<fstream>
#include<vector>
#include<string>
#include<cmath>

using namespace std;

string ParseData(vector<string> &Clauses, vector<string> &Restore);
void RestoreClauses(vector<string> &Clauses, vector<string> &Restore);
void BCP(vector<string> &Clauses);
bool DPLL(vector<string> &Clauses,vector<string> Guesses, vector<vector<bool>> &TT, string vars, int index1);
void ReduceClause(vector<string> &Clauses);
string choose(vector<string> &Clauses,string vars);
void CreateTT(vector<vector<bool>> &TT, int shift, int combos);
void CreateFormula();

int main()
{
	vector<string> Clauses;
	vector<string> Guesses;
	vector<string> Restore;

	vector<vector<bool>> TT;
	int shift;
	int combos = 1;
	int cnt = 0;
	bool answer = false;
	string Variables;
	int n = 5;
	//CreateFormula();
	
	Variables = ParseData(Clauses,Restore);

	shift = Variables.size();
	combos = (combos << shift);

	CreateTT(TT,shift,combos);

	for(int index1 = 0; index1 < combos && answer == false; index1++)
	{
	answer = DPLL(Clauses,Guesses,TT,Variables,index1);

	if(answer)
	{
		for(int i = 0; i < shift; i++)
		{
			cout << TT[index1][i];
			cnt++;
			if(cnt == n)
			{
				cnt = 0;
				cout << endl;
			}
		}
	}
	else
		cout << "Unsatisfiable" << endl;

	RestoreClauses(Clauses,Restore);
	}
	
	return 0;
}
void CreateFormula()
{
	string variables = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#$%^*<>,./?;:[]`~";
	const int size = 5;
	int tempsize = size;
	string clause;
	string var;
	string var2;
	ofstream ReadOut;
	string arr[size][size];
	int cnt = 0;
	int cnt2 = 0;
	int cnt3 = 0;
	int cnt4 = 0;


	ReadOut.open("formula.txt");

	if(ReadOut.fail())
		cout << "Error Opening the file";
	else
	{
		for(int i = 0; i < size; i++)
		{
			clause = "(";
			for(int k = 0; k < size; k++)
			{
				clause = clause + variables[cnt] + " | ";
				cnt++;
			}

			clause = clause + ") ";
			clause.erase(clause.find(')') - 3,3);
			ReadOut << clause;
			ReadOut << " & ";
			clause.clear();
		}
		cnt = 0;
		for(int i = 0; i < size; i++)
		{
			for(int k = 0; k < size - 1; k++)
			{
				cnt2=cnt + 1;
				while(cnt2 < tempsize)
				{
					clause = "(" + clause + "-" + variables[cnt] + " | -" + variables[cnt2] + ")";
					ReadOut << clause;
					ReadOut << " & ";
					clause.clear();
					cnt2++;
				}
				cnt = ++cnt;
				cnt2 = ++cnt3;

			}
			tempsize+=size;
			cnt = ++cnt4 * size;
			cnt2 = 0;
			cnt3 = 0;
		}
		cnt = 0;
		cnt2 = 0;
		cnt3 = 0;
		cnt4 = 0;
		for(int i = 0; i < size; i++)
		{
			for(int k = 0; k < size - 1; k++)
			{
				cnt2=size + cnt;
				while(cnt2 < (size*size))
				{
					clause = "(" + clause + "-" + variables[cnt] + " | -" + variables[cnt2] + ")";
					ReadOut << clause;
					ReadOut << " & ";
					clause.clear();
					cnt2 += size;
				}
				cnt = cnt + size;
				cnt2 = ++cnt3 * size;
			}
			cnt = ++cnt4;
			cnt2 = 0;
			cnt3 = 0;
		}

		cnt = 0;
		cnt2 = 1;
		cnt3 = 0;
		for(int i = 0; i < size; i++)
		{
			for(int k = 0; k < size; k++)
			{
				arr[i][k] = variables[cnt];
				cnt++;
			}
		}
		for(int i = 0; i < size; i++)
		{
			for(int k = 0; k < size; k++)
			{
				if(i + 1 < size && k + 1 < size)
				{
					while((i + cnt2) < size && (k + cnt2) < size)
					{

						clause = "(-" + arr[i][k] + " | -" +arr[i+cnt2][k + cnt2] + ")";
						ReadOut << clause;
						ReadOut << " & ";
						clause.clear();
						cnt2++;

					}
					cnt2 = 1;
				}
			}
		}
		cnt = 0;
		cnt2 = 1;
		cnt3 = 0;
		var2.clear();
		for(int i = 0; i < size; i++)
		{
			for(int k = 0; k < size; k++)
			{

				if(var2.find(arr[i][k]) == -1)
				{
					if(i + 1 < size && k - 1 >= 0)
					{

						while((i + cnt2) < size && (k - cnt2) >= 0)
						{

							clause = "(-" + arr[i][k] + " | -" +arr[i+cnt2][k - cnt2] + ")";
							ReadOut << clause;
							ReadOut << " & ";
							clause.clear();
							cnt2++;

						}
						cnt2 = 1;
					}
				}
			}
		}

		ReadOut.close();
	}


}
void CreateTT(vector<vector<bool>> &TT, int shift, int combos)
{
	int cnt1 = 0;
	int cnt2 = 0;
	int cnt3 = 1;

	TT.resize(combos);
	for(int i = 0; i < combos; i++)
		TT[i].resize(shift);

	for(int i = shift - 1 ; i >= 0; i--)
	{
		for(int k = 0; k < combos; k++)
		{
			if(cnt1 < cnt3)
			{
				TT[k][i] = 1;
				cnt1++;
				if(cnt1 == cnt3)
					cnt2 = 0;
			}
			else if(cnt2 < cnt3)
			{
				TT[k][i] = 0;
				cnt2++;
				if(cnt2 == cnt3)
					cnt1 = 0;
			}
		}
		cnt3 = cnt3 * 2;

	}
}
string ParseData(vector<string> &Clauses, vector<string> &Restore)
{
	ifstream ReadIn;
	string StringIn;
	string SingleClause;
	string Variables;
	char CharIn;
	ReadIn.open("formula.txt");

	if(ReadIn.fail())
	{
		cout << "Error Reading the file!" << endl;
	}
	else
	{
		ReadIn >> CharIn;
		while(!ReadIn.eof())
		{
			if(isalpha(CharIn))
			{
				if(Variables.find(CharIn) == -1)
				{
					Variables = Variables + CharIn;
				}
			}
			if(CharIn != '&' && CharIn != '(' && CharIn != ')' && CharIn !='|')
			{
				StringIn = StringIn + CharIn;
			}
			else if (CharIn == '&')
			{
				Clauses.push_back(StringIn);
				Restore.push_back(StringIn);
				StringIn.clear();
			}

			ReadIn >> CharIn;
		}
		Clauses.push_back(StringIn);
		Restore.push_back(StringIn);
	}
	ReadIn.close();

	return Variables;
}
void RestoreClauses(vector<string> &Clauses, vector<string> &Restore)
{
	Clauses.clear();
	for(int i = 0; i < Restore.size(); i++)
	{
		Clauses.push_back(Restore[i]);
	}
}
void BCP(vector<string> &Clauses)
{
	string tempClause;
	string tempClause2;
	bool resolve = false;
	int index;
	for(int i = 0; i < Clauses.size(); i++)
	{
		tempClause = Clauses[i];
		//Look for a unit clause
		if(tempClause.size() == 1)
		{
			//sift through clauses if resolution can be done
			for(int k = 0; k < Clauses.size(); k++)
			{
				tempClause2 = Clauses[k];
				index = Clauses[k].find(tempClause[0]);
				//check if the negation of the literal exits in the other clauses
				if(index > 0 && tempClause2[index - 1] == '-')
				{
					tempClause2.erase(index - 1, 2);
					Clauses[k] = tempClause2;
					resolve = true;
					Clauses[i] = "0";
				}
			}
		}
	}
	//eliminate the clause
	if(resolve)
		ReduceClause(Clauses);

}
bool DPLL(vector<string> &Clauses,vector<string> Guesses,vector<vector<bool>> &TT, string vars, int index1)
{
	string choices;
	static string maxChoices;
	string tempClause;
	int index;
	bool choice;
	static bool ans;
	static int index2 = 0;
	static int index4 = 0;
	bool flag = false;

	BCP(Clauses);

	if(Clauses.empty())
	{
		index2 = 0;
		index4 = 0;
		ans =  true;
		return ans;
	}
	else if(Clauses[0] == "")
	{
		index2 = 0;
		index4 = 0;
		ans = false;

		return ans;
	}
	else
	{
		//choices = choose(Clauses,vars);
		choices = vars[index4];
		index4++;
		choice = TT[index1][index2];
		index2++;

		if(choice == 1)
		{
			for( int i = 0; i < Clauses.size(); i++)
			{
				tempClause = Clauses[i];
				index = tempClause.find(choices[0]);

				if( index > 0 && tempClause[index - 1] == '-')
				{
					tempClause.erase(index - 1, 2);
					Clauses[i] = tempClause;
				}
				else if(index > -1)
				{
					Clauses[i] = "0";
					flag = true;
				}
			}
			if(flag)
			{
				flag = false;
				ReduceClause(Clauses);
			}
		}
		else
		{
			for( int i = 0; i < Clauses.size(); i++)
			{
				tempClause = Clauses[i];
				index = tempClause.find(choices[0]);

				if( index > 0 && tempClause[index - 1] == '-')
				{               
					Clauses[i] = "0";
					flag = true;
				}
				else if(index > -1)
				{
					tempClause.erase(index, 1);
					Clauses[i] = tempClause;
				}
			}
			if(flag)
			{
				flag = false;
				ReduceClause(Clauses);
			}

		}
		return DPLL(Clauses,Guesses,TT,vars,index1);
	}

}
void ReduceClause(vector<string> &Clauses)
{
	vector<string> newClauses;
	for(int i = 0; i < Clauses.size(); i++)
	{
		if(Clauses[i] != "0")
		{
			newClauses.push_back(Clauses[i]);
		}
	}
	Clauses.clear();

	for(int i = 0; i < newClauses.size(); i++)
	{
		Clauses.push_back(newClauses[i]);
	}

}
string choose(vector<string> &Clauses, string vars)
{
	string vars2;
	string vars3;
	string vars4;
	string tempClause;

	for(int i = 0; i < Clauses.size(); i++)
	{
		tempClause = Clauses[i];
		for(int k = 0; k < Clauses[i].size(); k++)
		{
			if(isalpha(tempClause[k]) && vars4.find(tempClause[k]) == -1)
				vars4 = vars4 + tempClause[k];
		}
	}

	return vars4;
}
/*
So Far at N = 4
Result:
0100
0001
1000
0010

*/