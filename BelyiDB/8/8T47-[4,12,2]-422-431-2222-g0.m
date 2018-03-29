s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T47-[4,12,2]-422-431-2222-g0";
s`BelyiDBFilename := "8T47-[4,12,2]-422-431-2222-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 12, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 8, 4, 5, 6, 7, 1 ],
\[ 1, 3, 2, 4, 5, 6, 7, 8 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 1152 > |
[ 6, 5, 7, 8, 2, 3, 1, 4 ],
[ 1, 3, 8, 6, 4, 7, 5, 2 ],
[ 6, 7, 4, 3, 8, 1, 2, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 6, 5, 7, 8, 2, 3, 1, 4 ],
\[ 1, 3, 8, 6, 4, 7, 5, 2 ],
\[ 6, 7, 4, 3, 8, 1, 2, 5 ]:
 Order := 1152 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 6, 5, 7, 8, 2, 3, 1, 4 ],
\[ 1, 3, 8, 6, 4, 7, 5, 2 ],
\[ 6, 7, 4, 3, 8, 1, 2, 5 ]:
 Order := 1152 >) |
[ PermutationGroup<8 |  
\[ 6, 5, 7, 8, 2, 3, 1, 4 ],
\[ 1, 3, 8, 6, 4, 7, 5, 2 ],
\[ 6, 7, 4, 3, 8, 1, 2, 5 ]:
 Order := 1152 > |
[ 6, 5, 7, 8, 2, 3, 1, 4 ],
[ 2, 8, 1, 5, 7, 6, 4, 3 ],
[ 5, 4, 6, 2, 1, 3, 8, 7 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 8, 4, 5, 6, 7, 1 ],
\[ 1, 3, 2, 4, 5, 6, 7, 8 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 1152 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 8, 4, 5, 6, 7, 1 ],
\[ 1, 3, 2, 4, 5, 6, 7, 8 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 1152 > |
[ 6, 5, 7, 8, 2, 3, 1, 4 ],
[ 1, 3, 8, 6, 4, 7, 5, 2 ],
[ 6, 7, 4, 3, 8, 1, 2, 5 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
