#include<iostream>
#include<fstream>
#include<vector>
#include<string>
#include<cmath>

using namespace std;

string ParseData(vector<string> &Clauses, vector<string> &Restore);
void RestoreClauses(vector<string> &Clauses, vector<string> &Restore);
void BCP(vector<string> &Clauses);
bool DPLL(vector<string> &Clauses, vector<vector<bool>> &TT, string vars, int index1);
void ReduceClause(vector<string> &Clauses);
void CreateTT(vector<vector<bool>> TT, int shift, vector<string> &Clauses, string vars, vector<string> &Restore);
void CreateFormula();

int main()
{
	vector<string> Clauses;
	vector<string> Restore;
	vector<vector<bool>> TTarray;

	int shift;
	int combos = 1;
	int cnt = 0;
	string Variables;

	//Create propositional formula
	//CreateFormula();

	//Determine the set of variables
	Variables = ParseData(Clauses,Restore);

	//capture the number of variables before variables is manipulated
	shift = Variables.size();

	//CreatTT originally produced a truth table
	//Now a truth table is created on the fly and the values for each variable is run through DPLL
	CreateTT(TTarray,shift,Clauses, Variables, Restore);

	return 0;
}
//Function: CreateTT()
//Input: Truth Table vector, # of variables, Clauses of formula, list of variables, copy of clauses
//Output: 
//Description: Creates Truth Table row on the fly and invokes DPLL to determine satisfiability
void CreateTT(vector<vector<bool>> TT, int shift,vector<string> &Clauses, string vars, vector<string> &Restore)
{
	int cnt = 1;
	int cnt1 = 0;
	int cnt2 = 0;
	int cnt4 = 0;
	int modval = 1;
	const int size = shift;
	int N = 4;
	int RowReturn = 0;
	bool swap = true;
	vector<int> modvals;
	vector<int> negation;
	bool answer = false;

	//Make the truth table vectore only 1 row
	TT.resize(1);
	//Create a vector that will hold mod values for each variable
	modvals.resize(1);
	//store flag for each variable when it must toggle truth value
	negation.resize(1);

	for(int i = 0; i < 1 ; i++)
	{
		TT[i].resize(shift);
		modvals.resize(shift);
		negation.resize(shift);
	}

	//Set initial mod value and truth value 
	modvals[shift - 1] = 1;
	negation[shift -1] = 1;

	//Determine the modular values for each variable
	for(int i = shift - 2; i >= 0; i--)
	{
		modval = modval * 2;
		modvals[i] = modval;
		negation[i] = 1;

	}

	//Continue creating truth table values until the truth values satisfy the formula
	while(!answer)
	{
		for(int i = 0; i < shift; i++)
		{
			if(negation[i] &&  cnt % modvals[i]  != 0)
			{
				TT[0][i] = 1;
			}
			else if(negation[i] &&  cnt % modvals[i]  == 0)
			{
				negation[i] = false;
				TT[0][i] = 1;
			}
			else if(!negation[i] && cnt % modvals[i] != 0)
			{
				TT[0][i] = 0;
			}
			else if(!negation[i] && cnt % modvals[i] == 0)
			{
				negation[i] = true;
				TT[0][i] = 0;
			}
		}
		cnt++;
		//invoke the recurisive DPLL
		answer = DPLL(Clauses,TT,vars,0);

		//If the formula has been satisfied then display the values
		//otherwise, output a count value to indicate where in the truth table the algorithm is
		if(answer)
		{
			for(int i = 0; i < shift; i++)
			{
				cout << TT[0][i];
				RowReturn++;
				if(RowReturn == N)
				{
					RowReturn = 0;
					cout << endl;
				}
			}
		}
		else
		{
			cout << ++cnt4 << endl;
		}
		//Restore the vector of clauses for the next truth table section
		RestoreClauses(Clauses,Restore);
	}
}
//Function: RestoreClauses()
//Input: Clauses of formula, copy of clauses
//Output: 
//Description: Gives clauses its original contents
void RestoreClauses(vector<string> &Clauses, vector<string> &Restore)
{
	Clauses.clear();
	//Travers through restore and give each of its value to Clauses
	for(int i = 0; i < Restore.size(); i++)
	{
		Clauses.push_back(Restore[i]);
	}
}
//Function: DPLL()
//Input: Clauses of formula, row of a truth table, list of variables, index into the truth table
//Output: 
//Description: Looks for unit true clauses and reduces clause using unit resolution
bool DPLL(vector<string> &Clauses,vector<vector<bool>> &TT, string vars, int index1)
{
	string choices;
	string tempClause;
	int index;
	bool choice;
	static bool ans;
	static int index2 = 0;
	static int index4 = 0;
	bool flag = false;

	//Recuce any clauses that can be reduced through unit resolution
	BCP(Clauses);

	//base case 1: If the clauses vector is empty then it indicates the formula is satisfiable
	//reset values and return true
	//base case 2: if the clauses vector contains an empty clause then the formula is not satisfiable
	//reset values and reurn false
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
		//choose a variable from the list
		choices = vars[index4];
		index4++;
		//obtain its truth value
		choice = TT[index1][index2];
		index2++;

		//If the choice is true
		if(choice == 1)
		{
			//traverse through the clauses
			for( int i = 0; i < Clauses.size(); i++)
			{
				tempClause = Clauses[i];
				index = tempClause.find(choices[0]);
				//lazy delete the claues that have the variable as true
				//reduce the variables that have the variable as false
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
			//delete clauses that have "0"
			if(flag)
			{
				flag = false;
				ReduceClause(Clauses);
			}
		}
		else
		{
			//if the choice is false
			//traverse through the clause
			for( int i = 0; i < Clauses.size(); i++)
			{
				
				tempClause = Clauses[i];
				index = tempClause.find(choices[0]);
				//lazy delete the clauses that have the variable as false
				//reduce the clauses that have the variale as true
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
			//delete clauses that have "0"
			if(flag)
			{
				flag = false;
				ReduceClause(Clauses);
			}

		}
		//recursive call
		return DPLL(Clauses,TT,vars,index1);
	}

}
//Function: BCP()
//Input: Clauses of formula
//Output: 
//Description: Looks for unit true clauses and reduces clause using unit resolution
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
//Function: BCP()
//Input: Clauses of formula
//Output: 
//Description: Reduces the lazy deleted clauses
void ReduceClause(vector<string> &Clauses)
{
	vector<string> newClauses;
	//traverses the clauses for lazy deleted clauses
	//eliminiates the clause
	for(int i = 0; i < Clauses.size(); i++)
	{
		if(Clauses[i] != "0")
		{
			newClauses.push_back(Clauses[i]);
		}
	}
	Clauses.clear();
	//restore the clause
	for(int i = 0; i < newClauses.size(); i++)
	{
		Clauses.push_back(newClauses[i]);
	}

}
//Function: ParseData()
//Input: Clauses (S)
//Output: variables
//Description: This function parses a propositional formula in the text file formula.txt
string ParseData(vector<string> &Clauses, vector<string> &Restore)
{
	ifstream ReadIn;
	string StringIn;
	string SingleClause;
	string Variables;
	char CharIn;

	//open file
	ReadIn.open("formula.txt");
	//Throw error if file does not open
	if(ReadIn.fail())
	{
		cout << "Error Reading the file!" << endl;
	}
	else
	{
		//Read first character
		ReadIn >> CharIn;
		while(!ReadIn.eof())
		{
			//read in each variable and store in a string
			if(isalpha(CharIn))
			{
				if(Variables.find(CharIn) == -1)
				{
					Variables = Variables + CharIn;
				}
			}
			//Reach each character until you get &, indicating the end of each clause
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
		//place each clause in Clauses and Restore
		Clauses.push_back(StringIn);
		Restore.push_back(StringIn);
	}
	ReadIn.close();

	return Variables;
}
//Function: CreateFormula()
//Input:
//Output: 
//Description: Creates Proposional Formula based on number of N queens
//Algorith is currently set to go up to N = 8, but can be extended by intorducing more variables
void CreateFormula()
{
	 //Declare variables for queen
   string variables = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@";
   const int size = 4;
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

   //Open file
   ReadOut.open("formula.txt");

   //Ensure file opens
   if(ReadOut.fail())
      cout << "Error Opening the file";
   else
   {
      //Produce the clauses where all values in each row may exist
      for(int i = 0; i < size; i++)
      {
         clause = "(";
         for(int k = 0; k < size; k++)
         {
            clause = clause + variables[cnt] + " | ";
            cnt++;
         }
         //Eliminate any unncessary end additions
         clause = clause + ") ";
         clause.erase(clause.find(')') - 3,3);
         ReadOut << clause;
         ReadOut << " & ";
         clause.clear();
      }
      cnt = 0;
      
      // Create clauses to ensure only one variable is true in each row
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
      //Create clauses to ensure only one variable is true in each column
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
      //Create claues to ensure only one variable is true in each right diagnol
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
      //Create claues to ensure only one variable is true in each left diagnol
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

/*
So Far at N = 4
Result:
0100
0001
1000
0010

*/