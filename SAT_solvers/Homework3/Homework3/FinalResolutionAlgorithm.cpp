#include<iostream>
#include<fstream>
#include<vector>
#include<string>

using namespace std;

string ParseData(vector<string> &Clauses);
void ReduceClause(vector<string> &Clauses);
void Resolution(vector<string>&Clauses, vector<string> &JClauses, vector<string> &UClauses, vector<string> &NotJClauses, string &variables, vector<string> &Inspection);
bool FindReduction(string clause, string vars);
string ReduceUClause(string Clause,char var);
void FindAssignments(vector<string> &Inspection, vector<string> &assign, string vars);
void CreateFormula();
void FormatOutput(vector<string> &assign, string vars, int size);

int main()
{
   vector<string> Clauses;
   vector<string> JClauses;
   vector<string> UClauses;
   vector<string> NotJClause;
   vector<string> InspectJ;
   vector<string> assign;

   int rounds;
   string variables;
   string formatVars;

   //Generates the formula, but has an extra & at the end that I just manually delete
   //CreateFormula();
   
   //Parse the data and figure out the number of variables
   variables = ParseData(Clauses);
   formatVars = variables;
   rounds = variables.size();

   //Run resolution for the # of the variables in the data set
   for(int i = 0; i < rounds; i++)
   {
      Resolution(Clauses, JClauses, UClauses, NotJClause, variables, InspectJ);
   }

   //If Sn at the end is empty then the formula is satisfiable, otherwise it is not
   if(Clauses.empty())
      cout << "Satisfiable" << endl;
   else
      cout << "Not Satisfiable" << endl;

   //Determine the truth values to each variable and display them
   FindAssignments(InspectJ, assign, variables);
   FormatOutput(assign, formatVars, 5);
   
   return 0;
}
//Function: ParseData()
//Input: Clauses (S)
//Output: variables
//Description: This function parses a propositional formula in the text file formula.txt
string ParseData(vector<string> &Clauses)
{
   ifstream ReadIn;
   string StringIn;
   string SingleClause;
   string Variables;
   char CharIn;

   //Open file
   ReadIn.open("formula.txt");
   //Throw error if file does not open
   if(ReadIn.fail())
   {
      cout << "Error Reading the file!" << endl;
   }
   else
   {
      //Read in first character
      ReadIn >> CharIn;


      while(!ReadIn.eof())
      {
         //Read in each variable and store in a string
         if(CharIn != '&' && CharIn != '(' && CharIn != ')' && CharIn !='|' && '-')
         {
            if(Variables.find(CharIn) == -1)
            {
               Variables = Variables + CharIn;
            }
         }
         //Read each character until you get &, indicating the end of each clause
         if(CharIn != '&' && CharIn != '(' && CharIn != ')' && CharIn !='|')
         {
            StringIn = StringIn + CharIn;
         }
         else if (CharIn == '&')
         {
            Clauses.push_back(StringIn);
            StringIn.clear();
         }

         ReadIn >> CharIn;
      }
      //Place each clause in Clauses(S)
      Clauses.push_back(StringIn);
   }
   return Variables;
}
//Function: Resolution()
//Input: Clauses (S), JClauses(J), UClauses(U), NotJClauses(-J), variabels, Inspection)
//Output: 
//Description: This function is the resolution algorithm that traves through S, J, U and reduces S until either an empty set or a set of an empty set
void Resolution(vector<string>&Clauses, vector<string> &JClauses, vector<string> &UClauses,vector<string> &NotJClauses, string &variables, vector<string> &Inspection)
{
   string clause;

   bool reduce;
   bool reduce2 = false;
   int cnt = 0;
   int cnt2;
   int cnt3;
   int index;
   bool satisfiable = false;
   string AllJClauses;
   bool flag1 = false;
   bool neg = false;
   string tempClause;
   string tempClause2;

   //Produce J 
   for(int i = 0; i < Clauses.size(); i++)
   {
      //check if a particular is in each clause in S
      if(Clauses[i].find(variables[cnt]) != -1)
      {
         //If it is, then add to J
         //Also, capture each clause to later inspect
         JClauses.push_back(Clauses[i]);
         AllJClauses = AllJClauses + Clauses[i] + " * ";
      }
      else
      {
         //If the variable is not in a clause in S, then add to -J
         NotJClauses.push_back(Clauses[i]);
      }
   }

   //Eliminate the '*'
   //'*' was used during debugging to maintain seperation between clauses
   if(!AllJClauses.empty())
   {
      AllJClauses.erase(AllJClauses.size() - 3, 3);
      Inspection.push_back(AllJClauses);
   }

   //Create set of U Clauses
   cnt3 = 0;
   cnt2 = 0;
   //If J is empty then there is nothing to add to U, so skip it
   if(JClauses.size() > 0)
   {
      //Traverse through each clause in J
      for(int i = JClauses.size() - 1; i >= 1; i--)
      {
         //cnt2 increases by one each round
         //the number of clauses to compare reduces by 1 each round
         cnt2 = cnt3;
         //find the location of a variable in a clause in J
         index = JClauses[i].find(variables[cnt]);
         tempClause = JClauses[i];

         //Determine if the variable is true or false
         //Mark a flag to signify if it is true of false
         if(index != 0 && tempClause[index-1] == '-')
            flag1 = true;
         else
            flag1 = false;

         //Traverse throught the list of JClauses
         while(cnt2 < JClauses.size() - 1)
         {
            //If the variable was true or false, then look for clauses with the negation of that variable
            if(flag1)
            {
               //look for the variable in the other clauses
               index = JClauses[cnt2+1].find(variables[cnt]);
               tempClause = JClauses[cnt2+1];

               //if the variable is false then merge with the clause traversing through J
               if(index == 0 || tempClause[index-1] != '-')
               {
                  
                  tempClause2 = JClauses[i] + JClauses[cnt2+1];
                  //eliminate the common variable that allowed the clauses to be merged
                  tempClause2 = ReduceUClause(tempClause2, variables[cnt]);
                  //check if a variable is true and false and eliminate the clause if this is the case
                  //otherwise, add it to U
                  reduce = FindReduction(tempClause2,variables);
                  if(!reduce)
                     UClauses.push_back(tempClause2);
               }
            }
            else
            {
               //look for the variable in the other clauses
               index = JClauses[cnt2+1].find(variables[cnt]);
               tempClause = JClauses[cnt2+1];

               //if the variable is ture then merge with the clause traversing through J
               if(index != 0 && tempClause[index - 1] == '-')
               {
                  tempClause2 = JClauses[i] + JClauses[cnt2+1];
                  //eliminate the common variable that allowed the clauses to be merged
                  tempClause2 = ReduceUClause(tempClause2, variables[cnt]);
                  //check if a variable is true and false and eliminate the clause if this is the case
                  //otherwise, add it to U
                  reduce = FindReduction(tempClause2,variables);
                  if(!reduce)
                     UClauses.push_back(tempClause2);
               }
            }
            cnt2++;
         }
         cnt3++;
      }
   }

   //get the next S set
   Clauses.clear();

   //Place -J in S
   for(int i = 0; i < NotJClauses.size(); i++)
   {
      Clauses.push_back(NotJClauses[i]);
   }
   //Place U in S, thus you have U union -J
   for(int i = 0; i < UClauses.size(); i++)
   {
      Clauses.push_back(UClauses[i]);
   }
   //clear the sets containing old information
   JClauses.clear();
   NotJClauses.clear();
   UClauses.clear();
   variables.erase(0,1);

}
//Function: FindReduction()
//Input: clause and vars
//Output: true of false
//Description: Determines if a clause can be eliminate since it has a variable both T and F
bool FindReduction(string clause,string vars)
{

   int identifier1 = 0;
   int identifier2 = 0;
   vector<int> indicies;
   bool reduce = false;

   //Traverse through the variables
   for(int i = 0; i < vars.size() && reduce == false; i++)
   {
      //Find the position of each variable in the clause and store in a vector for reference
      for(int j = 0; j < clause.length();j++)
      {
         if(clause[j] == vars[i])
         {
            indicies.push_back(j);
         }
      }
      //if there is more than one instance of a variable then it may potentially eliminates
      if(indicies.size() >=2)
      {
         for(int k = 0; k < indicies.size() && reduce == false; k++)
         {
            //Check if the variable is true and/or false
            //Use a flag to indicate for each truth value
            //If both flags are high then the clause is eliminated, thus output true
            //Otherwise, output false
            if(indicies[k] != 0)
            {
               if(clause[indicies[k]-1] == '-')
                  identifier1 = 1;
               else
                  identifier2 = 1;            
            }
            else
               identifier2 = 1;
            if(identifier1 == 1 && identifier2 == 1)
               reduce = true;
         }
      }
      //clear everything for later use
      indicies.clear();
      identifier1 = 0;
      identifier2 = 0;
   }

   return reduce;
}
//Function: ReduceUClause()
//Input: Clause in U, var that needs to be eliminated
//Output: string
//Description: Accepts a clause in U and eliminates the variable that allowed it to merge
string ReduceUClause(string Clause, char var)
{
   string tempClause;
   string tempNewClause;
   int find = 0;
   int cnt = 0;


   tempClause = Clause;
   //Find the variable in the clause that needs to be eliminated and erase it
   //Continue until all instances of that variable is eliminated
   find = tempClause.find(var);
   while(find != -1)
   {
      //find = tempClause.find(var);
      tempClause.erase(find,1);

      if( find != 0 && tempClause[find - 1] == '-')
         tempClause.erase(find-1,1);

      find = tempClause.find(var);
   }

   return tempClause;
}
//Function: FindAssignments()
//Input: Inspection(Union of all J), assign(variables to recieve boolean value), vars(list of all variables
//Output: 
//Description: This function traversed through the clauses in Inspection and determines the truth values
void FindAssignments(vector<string> &Inspection, vector<string> &assign, string vars)
{
   string tempClause;
   string tempClause2;
   string tempLiteral;
   string tempSign;
   string pureLiteral;
   string testClause;
   int index;
   string negative;
   bool notPure = false;
   bool pure = false;
   bool inAssign = false;
   string usedVars;
   vector<vector<string>> Clauses;
   vector<vector<string>> Restore;

   //resize assign to fit all the variables
   assign.resize(vars.size());

   for(int i = 0; i < assign.size() ; i++)
      assign[i].resize(2);

   // look at end of tempClause which is Ji-1
   tempClause = Inspection[Inspection.size() - 1];

   //search for a pure literal
   //if the size of the clause is 1 then the search is already finished
   if(tempClause.size() > 1)
   {
      //Traverse through each variable in the clause
      for(int l = 0; l < tempClause.size() && pure == false; l++)
      {
         //accept a variable
         if(isalpha(tempClause[l]))
         {
            //choose the first variable in the clause and compare it to the rest of the clauses
            //if it always T or always F, then it is a pure literal
            pureLiteral = tempClause[l];
            usedVars = usedVars + pureLiteral;
            index = tempClause.find(pureLiteral);
            if(tempClause.find(pureLiteral) != 0)
            {
               //negative is used as an indicator if the clause is true or false
               if(index != 0 && tempClause[index - 1] == '-')
                  negative = "0";
               else
                  negative = "1";
            }
            //travese through the clause comparing to the potential pure literal
            for( int k = 0; k < tempClause.size() && notPure == false; k++)
            {
               if(tempClause[k] == pureLiteral[0])
               {
                  //locate instances of the literal in the other clauses
                  //check their truth value and flag if the literal is not pure
                  index = tempClause.find(pureLiteral);

                  if(negative == "0" && index > 0)
                  {
                     if(tempClause[index - 1] == '-')
                     {
                        tempClause[index] = '0';
                        tempClause[index - 1] = '0';
                     }
                     else
                        notPure = true;
                  }
                  else
                  {
                     if(index > 0 && tempClause[index - 1] == '-')
                     {
                        notPure = true;
                     }
                     else
                        tempClause[index] = '0';
                  }
               }
            }
            //if the literal is pure then end the search
            if(!notPure)
               pure = true;
         }
      }
   }
   else
   {
      //if the clause is only size 1 then set this as a literal and make it true
      pureLiteral = tempClause;
      negative = "1";
   }

   //add the pure literal to assign and add its truth value
   assign.push_back(pureLiteral);
   assign.push_back(negative);

   Clauses.resize(Inspection.size());
   Restore.resize(Inspection.size());

   // Places clauses into 2-dim vector to make it more manageable
   for( int i = 0; i < Inspection.size(); i++)
   {
      tempClause = Inspection[i];

      for(int k = 0; k < Inspection[i].size(); k++)
      {
         if(tempClause[k] != '*' && tempClause != " ")
            testClause = testClause + tempClause[k];
         else if( tempClause[k] == '*')
         {
            Clauses[i].push_back(testClause);
            Restore[i].push_back(testClause);
            testClause.clear();
         }
      }
      //place inspection in a 2 vectors
      //one vector for manipulation and the other for reference
      Clauses[i].push_back(testClause);
      Restore[i].push_back(testClause);
      testClause.clear();
   }

   //Check if literal satisfies Clauses, if not then determine their assignment
   for( int i = Restore.size() - 1; i >= 0; i--)
   {
      //Traverse through each clause
      for(int k = 0; k < Restore[i].size(); k++)
      {
         //Traverse through each variable that has a truth value
         for(int j = 0; j < assign.size(); j++)
         {
            //determine if an assigned value exists in a clause
            tempClause2 = assign[j];
            if(isalpha(tempClause2[0]))
            {
               tempClause = Clauses[i][k];
               tempLiteral = assign[j];
               index = tempClause.find(tempLiteral);

               //if it does then lazy delete
               if( index != -1)
               {
                  if(assign[j+1] == "0" && index > 0 && tempClause[index - 1] == '-')
                     Clauses[i][k] = "0";
                  else if ( index == 0 || assign[j+1] == "1" && tempClause[index - 1] != '-')
                     Clauses[i][k] = "0";
               }
            }
         }
      }
      //Reduces the clauses that have been lazily deleted
      ReduceClause(Clauses[i]);

      //If the vector containing original clauses is emtpy then the other variables can be given arbitrary truth value
      if(Clauses[i].empty())
      {
         //Traverse through each clause
         for(int l = 0; l < Restore[i].size(); l++)
         {
            tempClause = Restore[i][l];
            //Traverse through each variable in the clause
            for( int f = 0; f < tempClause.size(); f++)
            {
               //Traverse through the assigned variables
               for( int m = 0; m < assign.size() && inAssign == false; m++)
               {
                  tempClause2 = assign[m];
                  //If the variable in the clause already has a value then skip it
                  if(isalpha(tempClause2[0]) && tempClause2.find(tempClause[f]) != -1 || !isalpha(tempClause[f]))
                     inAssign = true;
               }
               if(!inAssign)
               {
                  //If it does not have a value then set it to true
                  tempClause2 = tempClause[f];
                  assign.push_back(tempClause2);
                  assign.push_back("1");
               }
               inAssign = false;
            }

         }

      }
      else
      {
         //If the vector of clauses is not empty then determine values for the rest of variables
         //Traverse through each clause
         for(int p = 0; p < Clauses[i].size(); p++)
         {
            tempClause = Clauses[i][p];
            //Traverse through each variable in the clause
            for(int b = 0; b < tempClause.size(); b++)
            {
               //Traverse through each assigned variable
               for(int u = 0; u < assign.size() && inAssign == false; u++)
               {
                  //If the variable has a value then skip it
                  tempClause2 = assign[u];
                  if(isalpha(tempClause2[0]) && tempClause2.find(tempClause[b]) != -1 || !isalpha(tempClause[b]))
                     inAssign = true;
               }
               if(!inAssign)
               {
                  //If it does not have a value then determine its value and store in assign vector
                  tempClause2 = tempClause[b];
                  assign.push_back(tempClause2);
                  if( b != 0 && tempClause[b - 1] == '-')
                     assign.push_back("0");
                  else
                     assign.push_back("1");
               }
               inAssign = false;
            }

         }
      }

   }

}
//Function: ReduceClause()
//Input: Clauses(S)
//Output: 
//Description: Looks for "0" in (S), which indicates an eliminated clause
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
//Function: CreateFormula()
//Input:
//Output: 
//Description: Creates Proposional Formula based on number of N queens
//Algorith is currently set to go up to N = 8, but can be extended by intorducing more variables
void CreateFormula()
{
   //Declare variables for queen
   string variables = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@";
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
//Function: FormatOutput()
//Input: assign vector, vars, size
//Output: 
//Description: Takes the assign vector and outputs in nxn matrix to show where queens can be placed
void FormatOutput(vector<string> &assign, string vars, int size)
{
   bool foundIt = false;
   string temp;
   int newLine = 0;

   //Travers through each variable
   for( int i = 0; i < vars.size(); i++)
   {
      temp = vars[i];
      //find variable in assign and output its truth value
      for(int j = assign.size() - 1; j >= 0 && foundIt == false; j--)
      {
         if(assign[j] == temp)
         {
            foundIt = true;
            cout << assign[j+1] << " ";
            newLine++;
         }
         //Add a new line after each row
         if(newLine == size)
         {
            cout << endl;
            newLine = 0;
         }
      }
      foundIt = false;
   }
}
/*
Results:
N = 5
Satisfiable
0 1 0 0 0
0 0 0 1 0
1 0 0 0 0
0 0 1 0 0
0 0 0 0 1
*/